# search.py
import tkinter as tk
from tkinter import ttk, messagebox, filedialog, Menu
import subprocess
import socket
import threading
import ipaddress
from ping3 import ping
import concurrent.futures
import queue
from onvif import ONVIFCamera
import os
import json
from cryptography.fernet import Fernet
import openpyxl
import requests
from PIL import Image, ImageTk
import io
from urllib.parse import urlparse
import webbrowser
import platform
from zeroconf import ServiceBrowser, Zeroconf, ServiceListener
# from getmac import get_mac_address # Keep if MAC address is still desired without vendor lookup

# --- New Imports for Updates ---
from ttkthemes import ThemedTk
# from mac_vendor_lookup import MacLookup # Removed

# Global variable for the fixed encryption key
FIXED_ENCRYPTION_KEY = b'v8VZkq4W9E7RjTzOYKbLwSdXyGfChN3s1Mn2PpI0Qt6='

class BonjourListener(ServiceListener):
    """Listener for Bonjour/mDNS service discovery"""
    def __init__(self, app):
        self.app = app
        
    def add_service(self, zc, type_, name):
        info = zc.get_service_info(type_, name)
        if info:
            addresses = info.parsed_addresses()
            if addresses:
                ip = addresses[0]
                port = info.port
                # hostname = info.server # Hostname removed
                # Remove trailing dot from hostname if present
                # if hostname.endswith('.'):
                #     hostname = hostname[:-1]
                self.app.add_bonjour_device(ip, port) # Pass only ip and port
                
    def remove_service(self, zc, type_, name):
        pass
        
    def update_service(self, zc, type_, name):
        pass

class CmdToolExecutor:
    """
    A helper class to execute CMD commands in a separate thread
    and update a Tkinter Text widget.
    """
    def __init__(self, output_widget, root_after_callback):
        self.output_widget = output_widget
        self.root_after = root_after_callback

    def execute_command(self, command):
        self.root_after(0, lambda: self._update_output_gui(f"Executing: {command}\n\n", clear_previous=True))
        threading.Thread(target=self._run_command_in_thread, args=(command,), daemon=True).start()

    def _run_command_in_thread(self, command):
        try:
            creation_flags = subprocess.CREATE_NO_WINDOW if platform.system() == "Windows" else 0
            process = subprocess.run(
                command,
                shell=True,
                capture_output=True,
                text=True,
                check=False,
                encoding='utf-8',
                errors='replace',
                creationflags=creation_flags,
                timeout=60
            )
            output = process.stdout
            error_output = process.stderr
            self.root.after(0, self._update_output_gui, output, error_output)
        except subprocess.TimeoutExpired:
            self.root.after(0, self._update_output_gui, f"Command '{command}' timed out after 60 seconds.", "", is_error=True)
        except Exception as e:
            self.root.after(0, self._update_output_gui, f"Error executing command: {e}", "", is_error=True)

    def _update_output_gui(self, output, error_output="", clear_previous=False, is_error=False):
        self.output_widget.config(state=tk.NORMAL)
        if clear_previous:
            self.output_widget.delete(1.0, tk.END)
        
        self.output_widget.insert(tk.END, output)
        if error_output:
            self.output_widget.insert(tk.END, f"\n\n--- ERROR ---\n{error_output}")
        if is_error:
            self.output_widget.tag_configure("error", foreground="red")
            self.output_widget.insert(tk.END, "\n\n--- COMMAND FAILED ---\n", "error")

        self.output_widget.see(tk.END)
        self.output_widget.config(state=tk.DISABLED)

class RealTimeNetworkScanner:
    def __init__(self, root):
        self.root = root
        self.root.title("Advanced Network Scanner")
        self.root.state('zoomed')

        self.stop_flag = False
        self.search_thread = None
        self.scanning_active = False
        self.found_count = 0
        
        # Bonjour variables
        self.zeroconf = None
        self.bonjour_listener = None
        
        # --- New: Vendor Lookup --- (Removed)
        # self.mac_lookup = MacLookup() # Removed
        # self.vendor_nodes = {} # To store vendor parent nodes in treeview for grouping (Removed)
        
        # Floating message setup
        self.floating_message = ttk.Label(
            root, 
            text="", 
            background="#FFFFCC", 
            relief="solid", 
            borderwidth=1,
            padding=(5, 2, 5, 2),
            font=("Arial", 9)
        )
        self.floating_message.place(relx=1.0, rely=1.0, anchor='se', x=-10, y=-10)
        self.floating_message.place_forget()
        
        # --- Worker Queues ---
        self.onvif_queue = queue.Queue()
        self.onvif_threads = []
        self.port_scan_queue = queue.Queue()
        self.port_scan_threads = []

        # --- Encryption Setup ---
        try:
            self.cipher_suite = Fernet(FIXED_ENCRYPTION_KEY)
        except Exception as e:
            messagebox.showerror("Error", f"Encryption initialization error: {e}\nPlease ensure a valid encryption key is set.")
            self.root.destroy()
            return

        # --- Credential Management ---
        self.credential_sets = {} 
        self.camera_ip_to_cred_set = {} 

        # Cache for images
        self.thumbnail_cache = {} 
        self.hover_image_cache = {}

        # Create a small static image for the Treeview column
        self.camera_icon = None
        try:
            img = Image.new('RGB', (16, 16), color = 'green')
            self.camera_icon = ImageTk.PhotoImage(img)
        except Exception as e:
            print(f"Could not create camera icon: {e}")
            self.camera_icon = None

        # Hover image related variables
        self.hover_window = None
        self.hover_image_label = None
        self.current_hover_item = None
        self.current_hover_image_tk = None
        self.hover_image_thread = None
        self.last_hover_thread_id = 0

        # --- Scan Range & Settings Management ---
        self.scan_range = {"start_ip": "", "end_ip": ""}
        self.app_theme = "arc" # Default theme
        self.load_settings()
        self.load_camera_data()

        # --- Set Initial Theme ---
        try:
            self.root.set_theme(self.app_theme)
        except Exception:
            self.app_theme = "arc" # Fallback to a default theme
            self.root.set_theme(self.app_theme)

        
        self.create_widgets()
        self.setup_style()
        self.start_worker_threads()

    def center_window(self, window):
        """Centers a window on the screen"""
        window.update_idletasks()
        width = window.winfo_width()
        height = window.winfo_height()
        x = (window.winfo_screenwidth() // 2) - (width // 2)
        y = (window.winfo_screenheight() // 2) - (height // 2)
        window.geometry(f'+{x}+{y}')

    def show_floating_message(self, message):
        """Shows a temporary message in the bottom-right corner"""
        self.floating_message.config(text=message)
        self.floating_message.place(relx=1.0, rely=1.0, anchor='se', x=-10, y=-10)
        self.floating_message.lift()
        self.root.after(3000, self.hide_floating_message)
    
    def hide_floating_message(self):
        """Hides the floating message"""
        self.floating_message.place_forget()

    def encrypt_password(self, password):
        """Encrypts the password."""
        if not password:
            return ""
        return self.cipher_suite.encrypt(password.encode()).decode()

    def decrypt_password(self, encrypted_password):
        """Decrypts the password."""
        if not encrypted_password:
            return ""
        try:
            return self.cipher_suite.decrypt(encrypted_password.encode()).decode()
        except Exception as e:
            print(f"Decryption error: {e}")
            return "Decryption Failed"

    def load_camera_data(self):
        """Loads camera information and credential sets from file."""
        self.credential_sets = {
            "Default Admin": {"username": "admin", "password": self.encrypt_password("admin")}
        }
        self.camera_ip_to_cred_set = {}

        if os.path.exists('camera_data.json'):
            try:
                with open('camera_data.json', 'r') as f:
                    data = json.load(f)
                    if 'credential_sets' in data:
                        for name, creds in data['credential_sets'].items():
                            self.credential_sets[name] = {
                                'username': creds['username'],
                                'password': creds['password']
                            }
                    if 'camera_ip_to_cred_set' in data:
                        self.camera_ip_to_cred_set = data['camera_ip_to_cred_set']
            except json.JSONDecodeError as e:
                self.show_floating_message(f"Error reading camera_data.json: {e}")
            except Exception as e:
                self.show_floating_message(f"Error loading camera data: {e}")
        
    def save_camera_data(self):
        """Saves camera information and credential sets to file."""
        data = {
            'credential_sets': self.credential_sets,
            'camera_ip_to_cred_set': self.camera_ip_to_cred_set
        }
        try:
            with open('camera_data.json', 'w') as f:
                json.dump(data, f, indent=4)
        except Exception as e:
            self.show_floating_message(f"Error saving camera data: {e}")

    def load_settings(self):
        """Loads application settings, including scan range and theme, from file."""
        if os.path.exists('app_settings.json'):
            try:
                with open('app_settings.json', 'r') as f:
                    settings = json.load(f)
                    self.scan_range = settings.get('scan_range', {"start_ip": "", "end_ip": ""})
                    self.app_theme = settings.get('theme', 'arc') # Load theme
            except (json.JSONDecodeError, KeyError) as e:
                self.show_floating_message(f"Error reading app_settings.json: {e}")
            except Exception as e:
                self.show_floating_message(f"Error loading application settings: {e}")

    def save_settings(self):
        """Saves application settings, including scan range and theme, to file."""
        settings = {
            'scan_range': self.scan_range,
            'theme': self.app_theme # Save theme
        }
        try:
            with open('app_settings.json', 'w') as f:
                json.dump(settings, f, indent=4)
        except Exception as e:
            self.show_floating_message(f"Error saving application settings: {e}")

    def start_worker_threads(self):
        """Starts all worker threads (ONVIF and Port Scan)."""
        for _ in range(10):
            t = threading.Thread(target=self.onvif_worker, daemon=True)
            t.start()
            self.onvif_threads.append(t)
        for _ in range(20):
            t = threading.Thread(target=self.port_scan_worker, daemon=True)
            t.start()
            self.port_scan_threads.append(t)

    def onvif_worker(self):
        """ONVIF discovery worker."""
        while True:
            ip, item_id = self.onvif_queue.get()
            if self.stop_flag or not self.tree.exists(item_id):
                self.onvif_queue.task_done()
                continue
                
            self.root.after(0, self.update_status, f"Discovering ONVIF for {ip}")
            
            cred_set_name = self.camera_ip_to_cred_set.get(ip, "Default Admin")
            cred_info = self.credential_sets.get(cred_set_name)

            username = "admin"
            password = "admin"

            if cred_info:
                username = cred_info['username']
                password = self.decrypt_password(cred_info['password'])

            camera_status, rtsp_url, snapshot_uri = self.check_onvif_camera(ip, username, password)
            
            if camera_status == "Auth Failed" and cred_set_name != "Default Admin":
                default_cred_info = self.credential_sets.get("Default Admin")
                if default_cred_info:
                    default_username = default_cred_info['username']
                    default_password = self.decrypt_password(default_cred_info['password'])
                    camera_status, rtsp_url, snapshot_uri = self.check_onvif_camera(ip, default_username, default_password)
                    if camera_status == "ONVIF Found":
                        self.camera_ip_to_cred_set[ip] = "Default Admin"
                        self.save_camera_data()
                        cred_set_name = "Default Admin"
            
            self.root.after(0, self.update_camera_info, item_id, cred_set_name, rtsp_url, camera_status, snapshot_uri)
            self.onvif_queue.task_done()

    def port_scan_worker(self):
        """Port scanning worker."""
        while True:
            ip, item_id = self.port_scan_queue.get()
            if self.stop_flag or not self.tree.exists(item_id):
                self.port_scan_queue.task_done()
                continue
            
            common_ports = [80, 443, 554, 8080, 8000, 22, 23, 37777, 8899, 81]
            open_ports = []
            
            with concurrent.futures.ThreadPoolExecutor(max_workers=len(common_ports)) as executor:
                future_to_port = {executor.submit(self.scan_single_port, ip, port): port for port in common_ports}
                for future in concurrent.futures.as_completed(future_to_port):
                    port = future_to_port[future]
                    try:
                        if future.result():
                            open_ports.append(port)
                    except Exception:
                        pass
            
            open_ports.sort()
            self.root.after(0, self.update_open_ports, item_id, open_ports)
            self.port_scan_queue.task_done()

    def scan_single_port(self, ip, port):
        """Scans a single port on a given IP."""
        try:
            with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
                s.settimeout(0.5)
                s.connect((ip, port))
                return True
        except (socket.timeout, ConnectionRefusedError):
            return False
        except Exception:
            return False

    def check_onvif_camera(self, ip, username, password):
        """
        Checks for ONVIF camera presence and extracts RTSP and Snapshot URIs.
        """
        rtsp_url = ""
        snapshot_uri = ""
        try:
            cam = ONVIFCamera(ip, 80, username, password)
            media_service = cam.create_media_service()
            profiles = media_service.GetProfiles()
            if not profiles:
                return "No Profiles", "", ""
            
            token = profiles[0].token
            stream_uri = media_service.GetStreamUri({
                'StreamSetup': {'Stream': 'RTP-Unicast', 'Transport': 'RTSP'},
                'ProfileToken': token
            })
            rtsp_url = stream_uri.Uri

            try:
                imaging_service = cam.create_imaging_service()
                snapshot_uri_response = imaging_service.GetSnapshotUri({'ProfileToken': token})
                snapshot_uri = snapshot_uri_response.Uri
            except Exception as e:
                print(f"Error getting Snapshot URI for {ip}: {e}")
                snapshot_uri = ""

            return "ONVIF Found", rtsp_url, snapshot_uri
        except Exception as e:
            error_str = str(e).lower()
            if "unauthorized" in error_str or "401" in error_str:
                return "Auth Failed", "", ""
            elif "timed out" in error_str or "timeout" in error_str:
                return "Timeout", "", ""
            else:
                return "Error", "", str(e)

    def setup_style(self):
        self.style = ttk.Style()
        self.style.configure('red.TFrame', background='#ffcccc')
        self.style.configure('yellow.TFrame', background='#ffffcc')
        self.style.configure('purple.TFrame', background='#ffccff')
        self.style.configure('camera_found.TLabel', background='#ccffcc')
        self.style.configure('camera_error.TLabel', background='#ffcccc')
        self.style.configure('bonjour_device.TLabel', background='#cce5ff')
        self.style.configure('mac_dup.TLabel', background='#ffcc99')
        # Style for top-level vendor groups (Removed)
        # self.style.configure('group.TLabel', font=('TkDefaultFont', 9, 'bold'))


    def create_widgets(self):
        # --- New: Main Menu ---
        self.create_main_menu()
        
        main_frame = ttk.Frame(self.root)
        main_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)

        # Control Panel
        control_frame = ttk.Frame(main_frame)
        control_frame.pack(fill=tk.X, pady=5)

        self.search_btn = ttk.Button(
            control_frame,
            text="Search Network",
            command=self.start_search
        )
        self.search_btn.pack(side=tk.LEFT, padx=5)

        self.stop_btn = ttk.Button(
            control_frame,
            text="Stop Search",
            command=self.stop_search,
            state=tk.DISABLED
        )
        self.stop_btn.pack(side=tk.LEFT, padx=5)
        
        self.bonjour_btn = ttk.Button(
            control_frame,
            text="Scan Bonjour",
            command=self.start_bonjour_scan
        )
        self.bonjour_btn.pack(side=tk.LEFT, padx=5)

        self.manage_creds_btn = ttk.Button(
            control_frame,
            text="Manage Credentials",
            command=self.open_credential_manager
        )
        self.manage_creds_btn.pack(side=tk.LEFT, padx=5)

        self.manage_scan_range_btn = ttk.Button(
            control_frame,
            text="Manage Scan Range",
            command=self.open_scan_range_manager
        )
        self.manage_scan_range_btn.pack(side=tk.LEFT, padx=5)

        self.cmd_tools_btn = ttk.Button(
            control_frame,
            text="CMD Tools",
            command=self.open_cmd_tools_window
        )
        self.cmd_tools_btn.pack(side=tk.LEFT, padx=5)

        # Camera Credentials Selection Frame
        cred_selection_frame = ttk.Frame(control_frame)
        cred_selection_frame.pack(side=tk.RIGHT, padx=10)
        
        ttk.Label(cred_selection_frame, text="Credential Set:").pack(side=tk.LEFT)
        self.cred_set_var = tk.StringVar()
        self.cred_set_combobox = ttk.Combobox(
            cred_selection_frame,
            textvariable=self.cred_set_var,
            state="readonly",
            width=15
        )
        self.cred_set_combobox.pack(side=tk.LEFT, padx=5)
        self.cred_set_combobox.bind("<<ComboboxSelected>>", self.on_cred_set_selected)
        self.update_cred_combobox_options()
        
        self.apply_cred_btn = ttk.Button(
            cred_selection_frame,
            text="Apply to Selected IP",
            command=self.apply_camera_credentials
        )
        self.apply_cred_btn.pack(side=tk.LEFT, padx=5)

        # Progress Section
        self.progress_frame = ttk.Frame(main_frame)
        self.progress_frame.pack(fill=tk.X, pady=5)
        
        # --- New: Search/Filter Box ---
        search_frame = ttk.Frame(self.progress_frame)
        search_frame.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=5)
        ttk.Label(search_frame, text="Search:").pack(side=tk.LEFT)
        self.search_var = tk.StringVar()
        self.search_entry = ttk.Entry(search_frame, textvariable=self.search_var)
        self.search_entry.pack(side=tk.LEFT, fill=tk.X, expand=True)
        self.search_entry.bind("<KeyRelease>", self.filter_results)

        self.progress_label = ttk.Label(
            self.progress_frame,
            text="آماده برای اسکن..."
        )
        self.progress_label.pack(side=tk.LEFT)

        self.progress_bar = ttk.Progressbar(
            self.progress_frame,
            orient=tk.HORIZONTAL,
            mode='determinate'
        )
        self.progress_bar.pack(side=tk.RIGHT, fill=tk.X, expand=True)
        self.progress_bar.pack_forget()

        # Results Treeview (Modified for Grouping)
        tree_frame = ttk.Frame(main_frame)
        tree_frame.pack(fill=tk.BOTH, expand=True)

        # New "Vendor" column added (Removed)
        columns = ('IP', 'MAC', 'Credential Set', 'Open Ports', 'RTSP URL', 'Camera Status', 'Snapshot')
        self.tree = ttk.Treeview(tree_frame, columns=columns, show='headings') # Changed to show='headings'
        
        col_widths = {
            'IP': 120, 
            'MAC': 130, 
            # 'Hostname': 150, # Removed
            # 'Vendor': 150, # Removed
            'Credential Set': 120,
            'Open Ports': 120,
            'RTSP URL': 200,
            'Camera Status': 120,
            'Snapshot': 80
        }
        
        # We create the headings but the tree itself will only show top-level groups initially (Removed)
        # self.tree.heading("#0", text="Group / Vendor", anchor='w') # Removed
        # self.tree.column("#0", width=200, anchor='w') # Removed

        # Redefine the tree to show both headings and the grouping column (Removed)
        # self.tree.configure(show='tree headings') # Removed, now just 'headings'

        for col in columns:
            self.tree.heading(col, text=col, command=lambda c=col: self.sort_treeview_column(c, False))
            self.tree.column(col, width=col_widths.get(col, 100))

        scrollbar = ttk.Scrollbar(tree_frame, orient=tk.VERTICAL, command=self.tree.yview)
        self.tree.configure(yscroll=scrollbar.set)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        self.tree.pack(fill=tk.BOTH, expand=True)

        self.tree.tag_configure('ip_dup', background='#ffcccc')
        self.tree.tag_configure('camera_found', background='#ccffcc')
        self.tree.tag_configure('camera_error', background='#ffcccc')
        self.tree.tag_configure('bonjour_device', background='#cce5ff')
        self.tree.tag_configure('mac_dup', background='#ffcc99')
        
        self.tree.bind('<<TreeviewSelect>>', self.on_tree_select)
        self.tree.bind("<Button-3>", self.on_right_click)
        self.tree.bind("<Motion>", self._on_tree_motion)
        self.tree.bind("<Leave>", self._on_tree_leave)

        # Footer Section
        footer_frame = ttk.Frame(self.root)
        footer_frame.pack(side=tk.BOTTOM, fill=tk.X, pady=5)

        footer_text_part1 = "برنامه نویس : محمد علی عباسپور    "
        website_text = "intellsoft.ir"
        footer_text_part2 = " (نرم افزار تخصصی دوربین مداربسته)"
        
        self.footer_text_widget = tk.Text(
            footer_frame, 
            height=1, 
            wrap="word", 
            font=("Arial", 9),
            bg=self.root.cget('bg'),
            relief="flat",
            highlightthickness=0,
            cursor="arrow"
        )
        self.footer_text_widget.pack(side=tk.LEFT, padx=5)
        
        self.footer_text_widget.insert(tk.END, footer_text_part1)
        self.footer_text_widget.insert(tk.END, website_text, "link")
        self.footer_text_widget.insert(tk.END, footer_text_part2)

        self.footer_text_widget.tag_config("link", foreground="blue", underline=1)
        self.footer_text_widget.tag_bind("link", "<Button-1>", self._open_website_link)
        self.footer_text_widget.tag_bind("link", "<Enter>", self._on_link_enter)
        self.footer_text_widget.tag_bind("link", "<Leave>", self._on_link_leave)
        self.footer_text_widget.config(state="disabled")
        
    def create_main_menu(self):
        menubar = Menu(self.root)
        self.root.config(menu=menubar)

        # File Menu
        file_menu = Menu(menubar, tearoff=0)
        menubar.add_cascade(label="File", menu=file_menu)
        file_menu.add_command(label="Save Project", command=self.save_project)
        file_menu.add_command(label="Load Project", command=self.load_project)
        file_menu.add_separator()
        file_menu.add_command(label="Export to Excel", command=self.export_to_excel)
        file_menu.add_separator()
        file_menu.add_command(label="Exit", command=self.root.quit)

        # View Menu for Themes
        view_menu = Menu(menubar, tearoff=0)
        menubar.add_cascade(label="View", menu=view_menu)
        theme_menu = Menu(view_menu, tearoff=0)
        view_menu.add_cascade(label="Themes", menu=theme_menu)

        for theme in sorted(self.root.get_themes()):
            theme_menu.add_command(label=theme, command=lambda t=theme: self.change_theme(t))
            
    def change_theme(self, theme_name):
        try:
            self.root.set_theme(theme_name)
            self.app_theme = theme_name
            self.save_settings()
            self.show_floating_message(f"Theme changed to {theme_name}")
        except Exception as e:
            self.show_floating_message(f"Failed to set theme: {e}")

    def _open_website_link(self, event):
        webbrowser.open_new("http://intellsoft.ir")

    def _on_link_enter(self, event):
        self.footer_text_widget.config(cursor="hand2")

    def _on_link_leave(self, event):
        self.footer_text_widget.config(cursor="arrow")

    def start_bonjour_scan(self):
        """Starts Bonjour device discovery"""
        if not self.zeroconf:
            try:
                self.zeroconf = Zeroconf()
                self.bonjour_listener = BonjourListener(self)
                self.browser = ServiceBrowser(
                    self.zeroconf, 
                    ["_http._tcp.local.", "_onvif._tcp.local."],
                    self.bonjour_listener
                )
                self.show_floating_message("Bonjour scan started")
            except Exception as e:
                self.show_floating_message(f"Bonjour error: {str(e)}")
            
    def stop_bonjour_scan(self):
        """Stops Bonjour device discovery"""
        if self.zeroconf:
            self.zeroconf.close()
            self.zeroconf = None
            self.show_floating_message("Bonjour scan stopped")
            
    def add_bonjour_device(self, ip, port): # Removed hostname parameter
        """Adds a Bonjour device to the table"""
        existing = False
        # The logic for parent_node (vendor grouping) is removed as the tree is flat now.
        for child in self.tree.get_children():
            if self.tree.item(child, 'values')[0] == ip:
                existing = True
                break
        
        if not existing:
            device = {
                "IP": ip,
                "MAC": "N/A (Bonjour)",
                # "Hostname": hostname, # Removed
                # "Vendor": "Bonjour Device", # Removed
                "Credential Set": "Default Admin",
                "Open Ports": str(port),
                "RTSP URL": "",
                "Camera Status": "Bonjour Device",
                "Snapshot": "Unavailable"
            }
            # Since we don't have a MAC, we group it under a special vendor name (Comment removed as grouping is removed)
            item_id = self.add_device_to_tree(device)
            self.root.after(0, self.update_status, f"Bonjour device found: ({ip})") # Removed hostname from status message
            self.onvif_queue.put((ip, item_id))
            self.port_scan_queue.put((ip, item_id))

    def on_right_click(self, event):
        item_id = self.tree.identify_row(event.y)
        if not item_id: return
        
        # Check if it's a parent node or a child node (Removed as grouping is removed)
        # if self.tree.parent(item_id) == "": # This is a parent (vendor) node
        #     return # Or show a menu specific to the group
        
        column_id = self.tree.identify_column(event.x)
        if not column_id: return

        col_index = int(column_id.replace('#', '')) - 1
        columns = ('IP', 'MAC', 'Credential Set', 'Open Ports', 'RTSP URL', 'Camera Status', 'Snapshot') # Updated columns
        column_name = columns[col_index] if 0 <= col_index < len(columns) else None

        if not column_name: return

        cell_value = self.tree.item(item_id, 'values')[col_index]

        context_menu = Menu(self.root, tearoff=0)
        context_menu.add_command(label=f"Copy '{cell_value}'", command=lambda: self.copy_to_clipboard(cell_value))
        context_menu.post(event.x_root, event.y_root)

    def copy_to_clipboard(self, text):
        self.root.clipboard_clear()
        self.root.clipboard_append(text)
        self.show_floating_message(f"'{text}' copied to clipboard")

    def export_to_excel(self):
        # The loop iterates over all items in the tree, which will now be flat
        if not self.tree.get_children(): # Simplified check as no parent nodes exist
            self.show_floating_message("No data to export")
            return

        file_path = filedialog.asksaveasfilename(
            defaultextension=".xlsx",
            filetypes=[("Excel files", "*.xlsx"), ("All files", "*.*")],
            title="Save as Excel File"
        )
        if not file_path:
            return

        try:
            workbook = openpyxl.Workbook()
            sheet = workbook.active
            sheet.title = "Network Scan Results"

            # This will correctly get the new headers
            headers = [self.tree.heading(col)['text'] for col in self.tree['columns']]
            sheet.append(headers)

            # Iterate directly over all children, as there are no parent groups now
            for item_id in self.tree.get_children(): 
                values = self.tree.item(item_id, 'values')
                sheet.append(values)

            workbook.save(file_path)
            self.show_floating_message(f"Data exported to {file_path}")
        except Exception as e:
            self.show_floating_message(f"Error saving Excel: {e}")

    def update_cred_combobox_options(self):
        self.cred_set_combobox['values'] = list(self.credential_sets.keys())
        if self.cred_set_combobox['values']:
            self.cred_set_var.set(self.cred_set_combobox['values'][0])

    def on_cred_set_selected(self, event):
        pass

    def apply_camera_credentials(self):
        selected = self.tree.selection()
        if not selected:
            self.show_floating_message("Please select a camera")
            return
            
        item = selected[0]
        # Ignore if a parent group is selected (Removed as grouping is removed)
        # if self.tree.parent(item) == "": return

        values = self.tree.item(item, 'values')
        ip = values[0]
        
        selected_cred_set_name = self.cred_set_var.get()
        if not selected_cred_set_name or selected_cred_set_name not in self.credential_sets:
            self.show_floating_message("Please select a valid credential set")
            return

        self.camera_ip_to_cred_set[ip] = selected_cred_set_name
        self.save_camera_data()
            
        new_values = list(values)
        # The index for 'Credential Set' is now 2 (0:IP, 1:MAC, 2:Credential Set)
        if len(new_values) >= 3: 
            new_values[2] = selected_cred_set_name
            self.tree.item(item, values=new_values)
            self.onvif_queue.put((ip, item))
            self.show_floating_message("Credential set applied")
        else:
            self.show_floating_message("Invalid data structure")

    def on_tree_select(self, event):
        selected = self.tree.selection()
        if selected:
            item = selected[0]
            # Ignore if a parent group is selected (Removed as grouping is removed)
            # if self.tree.parent(item) == "": return
            values = self.tree.item(item, 'values')
            ip = values[0]
            associated_cred_set = self.camera_ip_to_cred_set.get(ip, "Default Admin")
            self.cred_set_var.set(associated_cred_set)

    def open_credential_manager(self):
        cred_manager_window = tk.Toplevel(self.root)
        cred_manager_window.title("Manage Credential Sets")
        self.center_window(cred_manager_window)
        cred_manager_window.transient(self.root)
        cred_manager_window.grab_set()

        input_frame = ttk.Frame(cred_manager_window, padding="10")
        input_frame.pack(fill=tk.X)

        ttk.Label(input_frame, text="Set Name:").grid(row=0, column=0, padx=5, pady=5, sticky="w")
        cred_name_var = tk.StringVar()
        cred_name_entry = ttk.Entry(input_frame, textvariable=cred_name_var, width=30)
        cred_name_entry.grid(row=0, column=1, padx=5, pady=5, sticky="ew")

        ttk.Label(input_frame, text="Username:").grid(row=1, column=0, padx=5, pady=5, sticky="w")
        cred_username_var = tk.StringVar()
        cred_username_entry = ttk.Entry(input_frame, textvariable=cred_username_var, width=30)
        cred_username_entry.grid(row=1, column=1, padx=5, pady=5, sticky="ew")

        ttk.Label(input_frame, text="Password:").grid(row=2, column=0, padx=5, pady=5, sticky="w")
        cred_password_var = tk.StringVar()
        cred_password_entry = ttk.Entry(input_frame, textvariable=cred_password_var, width=30, show='*')
        cred_password_entry.grid(row=2, column=1, padx=5, pady=5, sticky="ew")

        button_frame = ttk.Frame(cred_manager_window, padding="10")
        button_frame.pack(fill=tk.X)

        def add_cred_set():
            name = cred_name_var.get().strip()
            username = cred_username_var.get().strip()
            password = cred_password_var.get()

            if not name or not username:
                self.show_floating_message("Set name and username cannot be empty")
                return
            if name in self.credential_sets and name != "Default Admin":
                self.show_floating_message(f"Set '{name}' already exists")
                return
            
            encrypted_password = self.encrypt_password(password)
            self.credential_sets[name] = {"username": username, "password": encrypted_password}
            self.save_camera_data()
            update_cred_treeview()
            self.update_cred_combobox_options()
            self.show_floating_message(f"Credential set '{name}' added")
            cred_name_var.set("")
            cred_username_var.set("")
            cred_password_var.set("")

        def update_cred_set():
            selected = cred_tree.selection()
            if not selected:
                self.show_floating_message("Please select a credential set")
                return
            
            old_name = cred_tree.item(selected[0], 'values')[0]
            new_name = cred_name_var.get().strip()
            username = cred_username_var.get().strip()
            password = cred_password_var.get()

            if not new_name or not username:
                self.show_floating_message("Set name and username cannot be empty")
                return
            
            if old_name == "Default Admin" and new_name != "Default Admin":
                self.show_floating_message("Cannot change 'Default Admin' name")
                return

            if new_name != old_name and new_name in self.credential_sets:
                self.show_floating_message(f"Set '{new_name}' already exists")
                return

            encrypted_password = self.encrypt_password(password)

            if new_name != old_name:
                del self.credential_sets[old_name]
                for ip, name in list(self.camera_ip_to_cred_set.items()):
                    if name == old_name:
                        self.camera_ip_to_cred_set[ip] = new_name

            self.credential_sets[new_name] = {"username": username, "password": encrypted_password}
            self.save_camera_data()
            update_cred_treeview()
            self.update_cred_combobox_options()
            self.show_floating_message(f"Credentials '{old_name}' updated")
            cred_name_var.set("")
            cred_username_var.set("")
            cred_password_var.set("")

        def delete_cred_set():
            selected = cred_tree.selection()
            if not selected:
                self.show_floating_message("Please select a credential set")
                return
            
            name_to_delete = cred_tree.item(selected[0], 'values')[0]
            
            if name_to_delete == "Default Admin":
                self.show_floating_message("Cannot delete 'Default Admin'")
                return

            cameras_using_this_set = [ip for ip, name in self.camera_ip_to_cred_set.items() if name == name_to_delete]
            if cameras_using_this_set:
                confirm = messagebox.askyesno(
                    "Confirm Delete", 
                    f"Credential set '{name_to_delete}' is used by {len(cameras_using_this_set)} cameras.\nAre you sure you want to delete it? Affected cameras will revert to 'Default Admin'.", 
                    parent=cred_manager_window
                )
                if not confirm:
                    return
                for ip in cameras_using_this_set:
                    self.camera_ip_to_cred_set[ip] = "Default Admin"
                # Updated index for Credential Set
                for item_id in self.tree.get_children(): 
                    if self.tree.item(item_id, 'values')[0] == ip:
                        current_values = list(self.tree.item(item_id, 'values'))
                        current_values[2] = "Default Admin" # Adjusted index
                        self.tree.item(item_id, values=current_values)

            del self.credential_sets[name_to_delete]
            self.save_camera_data()
            update_cred_treeview()
            self.update_cred_combobox_options()
            self.show_floating_message(f"Credentials '{name_to_delete}' deleted")
            cred_name_var.set("")
            cred_username_var.set("")
            cred_password_var.set("")

        ttk.Button(button_frame, text="Add", command=add_cred_set).pack(side=tk.LEFT, padx=5, pady=5)
        ttk.Button(button_frame, text="Update", command=update_cred_set).pack(side=tk.LEFT, padx=5, pady=5)
        ttk.Button(button_frame, text="Delete", command=delete_cred_set).pack(side=tk.LEFT, padx=5, pady=5)

        cred_tree_frame = ttk.Frame(cred_manager_window, padding="10")
        cred_tree_frame.pack(fill=tk.BOTH, expand=True)

        cred_columns = ('Set Name', 'Username', 'Password')
        cred_tree = ttk.Treeview(cred_tree_frame, columns=cred_columns, show='headings')
        for col in cred_columns:
            cred_tree.heading(col, text=col)
            cred_tree.column(col, width=150)

        cred_scrollbar = ttk.Scrollbar(cred_tree_frame, orient=tk.VERTICAL, command=cred_tree.yview)
        cred_tree.configure(yscroll=cred_scrollbar.set)
        cred_scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        cred_tree.pack(fill=tk.BOTH, expand=True)

        def on_cred_tree_select(event):
            selected = cred_tree.selection()
            if selected:
                values = cred_tree.item(selected[0], 'values')
                cred_name_var.set(values[0])
                cred_username_var.set(values[1])
                cred_password_var.set("") # Do not display password directly

        cred_tree.bind('<<TreeviewSelect>>', on_cred_tree_select)

        def update_cred_treeview():
            for item in cred_tree.get_children():
                cred_tree.delete(item)
            for name, creds in self.credential_sets.items():
                decrypted_password_display = self.decrypt_password(creds['password'])
                cred_tree.insert('', tk.END, values=(name, creds['username'], decrypted_password_display))

        update_cred_treeview()

        close_button_frame = ttk.Frame(cred_manager_window, padding="10")
        close_button_frame.pack(fill=tk.X)
        ttk.Button(close_button_frame, text="Close", command=cred_manager_window.destroy).pack(side=tk.RIGHT, padx=5, pady=5)

        cred_manager_window.protocol("WM_DELETE_WINDOW", cred_manager_window.destroy)
        cred_manager_window.wait_window()

    def open_scan_range_manager(self):
        range_manager_window = tk.Toplevel(self.root)
        range_manager_window.title("Manage Scan Range")
        self.center_window(range_manager_window)
        range_manager_window.transient(self.root)
        range_manager_window.grab_set()

        input_frame = ttk.Frame(range_manager_window, padding="10")
        input_frame.pack(fill=tk.X)

        ttk.Label(input_frame, text="Start IP Address:").grid(row=0, column=0, padx=5, pady=5, sticky="w")
        self.start_ip_var = tk.StringVar(value=self.scan_range.get("start_ip", ""))
        start_ip_entry = ttk.Entry(input_frame, textvariable=self.start_ip_var, width=20)
        start_ip_entry.grid(row=0, column=1, padx=5, pady=5, sticky="ew")

        ttk.Label(input_frame, text="End IP Address:").grid(row=1, column=0, padx=5, pady=5, sticky="w")
        self.end_ip_var = tk.StringVar(value=self.scan_range.get("end_ip", ""))
        end_ip_entry = ttk.Entry(input_frame, textvariable=self.end_ip_var, width=20)
        end_ip_entry.grid(row=1, column=1, padx=5, pady=5, sticky="ew")

        button_frame = ttk.Frame(range_manager_window, padding="10")
        button_frame.pack(fill=tk.X)

        def save_range():
            start_ip = self.start_ip_var.get().strip()
            end_ip = self.end_ip_var.get().strip()

            if not start_ip and not end_ip:
                self.scan_range = {"start_ip": "", "end_ip": ""}
                self.save_settings()
                self.show_floating_message("Scan range cleared")
                return

            try:
                start_ip_obj = ipaddress.IPv4Address(start_ip)
                end_ip_obj = ipaddress.IPv4Address(end_ip)
                if start_ip_obj > end_ip_obj:
                    self.show_floating_message("Invalid IP range")
                    return
                self.scan_range = {"start_ip": start_ip, "end_ip": end_ip}
                self.save_settings()
                self.show_floating_message("Scan range saved")
            except ipaddress.AddressValueError:
                self.show_floating_message("Invalid IP format")
            except Exception as e:
                self.show_floating_message(f"Error: {str(e)}")

        ttk.Button(button_frame, text="Save Range", command=save_range).pack(side=tk.LEFT, padx=5, pady=5)
        ttk.Button(button_frame, text="Clear Range", command=lambda: [self.start_ip_var.set(""), self.end_ip_var.set(""), save_range()]).pack(side=tk.LEFT, padx=5, pady=5)
        ttk.Button(button_frame, text="Close", command=range_manager_window.destroy).pack(side=tk.RIGHT, padx=5, pady=5)

        range_manager_window.protocol("WM_DELETE_WINDOW", range_manager_window.destroy)
        range_manager_window.wait_window()

    def open_cmd_tools_window(self):
        cmd_window = tk.Toplevel(self.root)
        cmd_window.title("CMD Tools")
        self.center_window(cmd_window)
        cmd_window.transient(self.root)
        cmd_window.grab_set()

        cmd_frame = ttk.Frame(cmd_window, padding="10")
        cmd_frame.pack(fill=tk.BOTH, expand=True)

        ttk.Label(cmd_frame, text="Enter Command:").pack(padx=5, pady=5, anchor='w')
        command_entry = ttk.Entry(cmd_frame, width=80)
        command_entry.pack(fill=tk.X, padx=5, pady=5)

        output_text = tk.Text(cmd_frame, wrap="word", height=15, state=tk.DISABLED, bg="black", fg="white", font=("Courier New", 9))
        output_text.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)

        cmd_executor = CmdToolExecutor(output_text, self.root.after)

        def execute():
            command = command_entry.get().strip()
            if command:
                cmd_executor.execute_command(command)
            else:
                output_text.config(state=tk.NORMAL)
                output_text.delete(1.0, tk.END)
                output_text.insert(tk.END, "Please enter a command.")
                output_text.config(state=tk.DISABLED)

        button_frame = ttk.Frame(cmd_frame)
        button_frame.pack(fill=tk.X, pady=5)

        ttk.Button(button_frame, text="Execute", command=execute).pack(side=tk.LEFT, padx=5)
        ttk.Button(button_frame, text="Clear Output", command=lambda: output_text.config(state=tk.NORMAL) or output_text.delete(1.0, tk.END) or output_text.config(state=tk.DISABLED)).pack(side=tk.LEFT, padx=5)
        ttk.Button(button_frame, text="Close", command=cmd_window.destroy).pack(side=tk.RIGHT, padx=5)
        
        cmd_window.protocol("WM_DELETE_WINDOW", cmd_window.destroy)
        cmd_window.wait_window()

    def start_search(self):
        if self.scanning_active:
            self.show_floating_message("Scan already active.")
            return

        self.stop_flag = False
        self.scanning_active = True
        self.found_count = 0
        self.tree.delete(*self.tree.get_children())
        # self.vendor_nodes.clear() # Removed
        self.progress_bar.pack(side=tk.RIGHT, fill=tk.X, expand=True)
        self.update_status("Starting network scan...")
        self.search_btn.config(state=tk.DISABLED)
        self.stop_btn.config(state=tk.NORMAL)
        
        self.search_thread = threading.Thread(target=self._run_search_in_thread, daemon=True)
        self.search_thread.start()

    def stop_search(self):
        self.stop_flag = True
        self.scanning_active = False
        self.update_status("Scan stopped.")
        self.search_btn.config(state=tk.NORMAL)
        self.stop_btn.config(state=tk.DISABLED)
        self.progress_bar['value'] = 0
        self.progress_bar.pack_forget()

    def _run_search_in_thread(self):
        start_ip_str = self.scan_range.get("start_ip")
        end_ip_str = self.scan_range.get("end_ip")

        if not start_ip_str or not end_ip_str:
            self.root.after(0, self.show_floating_message, "Scan range not set. Please go to 'Manage Scan Range'.")
            self.root.after(0, self.stop_search)
            return

        try:
            start_ip = int(ipaddress.IPv4Address(start_ip_str))
            end_ip = int(ipaddress.IPv4Address(end_ip_str))
        except ipaddress.AddressValueError:
            self.root.after(0, self.show_floating_message, "Invalid IP address format in scan range.")
            self.root.after(0, self.stop_search)
            return

        total_ips = end_ip - start_ip + 1
        scanned_ips = 0

        max_workers = 50 # Adjust as needed
        with concurrent.futures.ThreadPoolExecutor(max_workers=max_workers) as executor:
            futures = {executor.submit(self._ping_ip, ipaddress.IPv4Address(i)): i for i in range(start_ip, end_ip + 1)}
            
            for future in concurrent.futures.as_completed(futures):
                if self.stop_flag:
                    break
                ip_int = futures[future]
                scanned_ip_str = str(ipaddress.IPv4Address(ip_int))
                scanned_ips += 1
                progress_value = (scanned_ips / total_ips) * 100
                self.root.after(0, self.update_progress, progress_value, f"Scanning: {scanned_ip_str}")
                
                try:
                    mac_address = future.result()
                    if mac_address:
                        # Hostname and Vendor lookup removed
                        # hostname = self.get_hostname(scanned_ip_str)
                        # vendor = self.get_mac_vendor(mac_address)
                        
                        device_data = {
                            "IP": scanned_ip_str,
                            "MAC": mac_address,
                            # "Hostname": hostname, # Removed
                            # "Vendor": vendor, # Removed
                            "Credential Set": "Default Admin",
                            "Open Ports": "Scanning...",
                            "RTSP URL": "N/A",
                            "Camera Status": "Searching...",
                            "Snapshot": "N/A"
                        }
                        self.root.after(0, self.add_device_to_tree, device_data)
                except Exception as e:
                    print(f"Error processing IP {scanned_ip_str}: {e}")

        self.root.after(0, self.finalize_scan)

    def _ping_ip(self, ip_address):
        """Pings an IP address and returns MAC if successful, None otherwise."""
        try:
            # ping3 returns float latency or False
            response = ping(str(ip_address), timeout=0.5, unit='ms')
            if response is not False:
                # get_mac_address is OS-dependent and can be slow/fail
                # You might need to adjust this based on your environment
                mac = get_mac_address(ip=str(ip_address))
                return mac if mac else "Unknown"
        except Exception:
            pass # Ping failed or MAC lookup failed
        return None

    def get_hostname(self, ip_address):
        """Attempts to resolve hostname from IP address."""
        try:
            # Hostname lookup removed as per user request
            return "N/A"
        except socket.gaierror:
            return "N/A"

    def get_mac_vendor(self, mac_address):
        """Looks up the vendor for a given MAC address."""
        # Vendor lookup removed as per user request
        return "N/A"

    def add_device_to_tree(self, device_data):
        """
        Adds a device to the treeview.
        This method will no longer group by vendor.
        """
        self.found_count += 1
        ip = device_data["IP"]
        mac = device_data["MAC"]
        # hostname = device_data["Hostname"] # Removed
        # vendor = device_data["Vendor"] # Removed
        cred_set = device_data["Credential Set"]
        open_ports = device_data["Open Ports"]
        rtsp_url = device_data["RTSP URL"]
        camera_status = device_data["Camera Status"]
        snapshot = device_data["Snapshot"]

        # No grouping, add directly as a top-level item
        item_id = self.tree.insert(
            '', tk.END, 
            values=(ip, mac, cred_set, open_ports, rtsp_url, camera_status, snapshot), # Updated values
            tags=('ip_dup',) if self.is_ip_duplicate(ip) else ()
        )

        self.update_status(f"Found {self.found_count} devices.")
        self.onvif_queue.put((ip, item_id))
        self.port_scan_queue.put((ip, item_id))
    
    def update_camera_info(self, item_id, cred_set_name, rtsp_url, camera_status, snapshot_uri):
        """Updates ONVIF camera specific info in the tree."""
        if not self.tree.exists(item_id): return

        current_values = list(self.tree.item(item_id, 'values'))
        
        # Update values based on new column order (IP, MAC, Credential Set, Open Ports, RTSP URL, Camera Status, Snapshot)
        # Assuming rtsp_url is at index 4, camera_status at 5, snapshot_uri at 6
        # And Credential Set is at index 2
        
        if len(current_values) >= 7: # Ensure enough columns
            current_values[2] = cred_set_name # Credential Set
            current_values[4] = rtsp_url # RTSP URL
            current_values[5] = camera_status # Camera Status
            current_values[6] = snapshot_uri # Snapshot URI
        
        self.tree.item(item_id, values=current_values)

        current_tags = list(self.tree.item(item_id, 'tags'))
        if camera_status == "ONVIF Found" and 'camera_found' not in current_tags:
            self.tree.item(item_id, tags=current_tags + ('camera_found',))
        elif camera_status != "ONVIF Found" and 'camera_found' in current_tags:
            self.tree.item(item_id, tags=[t for t in current_tags if t != 'camera_found'])

        if camera_status in ["Auth Failed", "Timeout", "Error"] and 'camera_error' not in current_tags:
            self.tree.item(item_id, tags=current_tags + ('camera_error',))
        elif camera_status not in ["Auth Failed", "Timeout", "Error"] and 'camera_error' in current_tags:
            self.tree.item(item_id, tags=[t for t in current_tags if t != 'camera_error'])
            
    def update_open_ports(self, item_id, open_ports):
        """Updates the Open Ports column in the treeview."""
        if not self.tree.exists(item_id): return
        current_values = list(self.tree.item(item_id, 'values'))
        if len(current_values) >= 4: # Assuming open ports is at index 3
            current_values[3] = ", ".join(map(str, open_ports)) if open_ports else "N/A"
        self.tree.item(item_id, values=current_values)

    def is_ip_duplicate(self, ip):
        """Checks if an IP already exists in the treeview."""
        for item_id in self.tree.get_children(): # Iterate directly over children
            if self.tree.item(item_id, 'values')[0] == ip:
                return True
        return False

    def get_child_items(self, parent_item):
        """Helper to get all children of a parent, including nested if any."""
        children = self.tree.get_children(parent_item)
        all_children = list(children)
        for child in children:
            all_children.extend(self.get_child_items(child))
        return all_children

    def sort_treeview_column(self, col, reverse):
        # Sorts only top-level items as grouping is removed
        data = [(self.tree.set(child, col), child) for child in self.tree.get_children('')]
        data.sort(reverse=reverse)
        for index, (val, item) in enumerate(data):
            self.tree.move(item, '', index)
        self.tree.heading(col, command=lambda: self.sort_treeview_column(col, not reverse))

    def update_status(self, message):
        self.progress_label.config(text=message)

    def update_progress(self, value, message):
        self.progress_bar['value'] = value
        self.update_status(message)

    def finalize_scan(self):
        self.stop_search()
        self.update_status(f"Scan finished. Found {self.found_count} devices.")
        self.progress_bar['value'] = 100
        self.show_floating_message(f"Scan finished. Found {self.found_count} devices.")

    def filter_results(self, event=None):
        query = self.search_var.get().lower()
        for item_id in self.tree.get_children(): # Iterate directly over children
            values = [str(v).lower() for v in self.tree.item(item_id, 'values')]
            
            # Check if query matches any of the remaining columns
            if any(query in v for v in values):
                self.tree.item(item_id, open=True, tags=('match',))
                self.tree.reattach(item_id, '', tk.END) # Bring matching items to bottom (or top if needed)
            else:
                self.tree.detach(item_id)
        
        # Bring non-matching items back if search query is empty
        if not query:
            all_items = self.tree.get_children('')
            for item_id in all_items:
                self.tree.reattach(item_id, '', tk.END)

    def _on_tree_motion(self, event):
        item_id = self.tree.identify_row(event.y)
        if not item_id:
            self._on_tree_leave(event)
            return

        # No snapshot display, so hover logic is removed
        pass

    def _on_tree_leave(self, event):
        # No snapshot display, so hover logic is removed
        pass

    def save_project(self):
        """Saves current device data to a JSON file."""
        file_path = filedialog.asksaveasfilename(
            defaultextension=".json",
            filetypes=[("Project Files", "*.json"), ("All Files", "*.*")],
            title="Save Project"
        )
        if not file_path:
            return

        results_to_save = []
        for item_id in self.tree.get_children(): # Iterate directly over children
            values = self.tree.item(item_id, 'values')
            # Adjust mapping based on new column structure
            device_data = {
                "IP": values[0],
                "MAC": values[1],
                # "Hostname": values[2], # Removed
                # "Vendor": values[3], # Removed
                "Credential Set": values[2], # New index
                "Open Ports": values[3], # New index
                "RTSP URL": values[4], # New index
                "Camera Status": values[5], # New index
                "Snapshot": values[6] # New index
            }
            results_to_save.append(device_data)

        try:
            with open(file_path, 'w') as f:
                json.dump(results_to_save, f, indent=4)
            self.show_floating_message(f"Project saved to {os.path.basename(file_path)}")
        except Exception as e:
            self.show_floating_message(f"Error saving project: {e}")

    def load_project(self):
        """Loads device data from a JSON file into the tree."""
        file_path = filedialog.askopenfilename(
            filetypes=[("Project Files", "*.json"), ("All Files", "*.*")],
            title="Load Project"
        )
        if not file_path:
            return

        try:
            with open(file_path, 'r') as f:
                loaded_data = json.load(f)

            # Clear current view before loading
            self.tree.delete(*self.tree.get_children())
            # self.vendor_nodes.clear() # Removed
            self.found_count = 0

            # Repopulate the tree with loaded data
            for device_data in loaded_data:
                self.found_count += 1
                self.add_device_to_tree(device_data) # This method needs to handle the new structure
            
            self.update_status(f"Project loaded. {self.found_count} devices.")
        except Exception as e:
            self.show_floating_message(f"Error loading project: {e}")

if __name__ == "__main__":
    # Use ThemedTk to get access to modern themes
    root = ThemedTk(theme="arc")
    app = RealTimeNetworkScanner(root)
    root.mainloop()