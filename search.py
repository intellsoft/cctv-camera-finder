# search.py
import tkinter as tk
from tkinter import ttk, messagebox, filedialog, Menu
import subprocess
import re
import socket
import threading
import ipaddress
from ping3 import ping
from datetime import datetime
import concurrent.futures
import queue
from onvif import ONVIFCamera
import time
import os
import json
from cryptography.fernet import Fernet
import base64
import openpyxl
import requests
from PIL import Image, ImageTk
import io
from urllib.parse import urlparse
import webbrowser
import platform
from zeroconf import ServiceBrowser, Zeroconf, ServiceListener
from getmac import get_mac_address # <-- کتابخانه جدید برای یافتن مک آدرس

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
                hostname = info.server
                # Remove trailing dot from hostname if present
                if hostname.endswith('.'):
                    hostname = hostname[:-1]
                self.app.add_bonjour_device(ip, port, hostname)
                
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
            self.root_after(0, self._update_output_gui, output, error_output)
        except subprocess.TimeoutExpired:
            self.root_after(0, self._update_output_gui, f"Command '{command}' timed out after 60 seconds.", "", is_error=True)
        except Exception as e:
            self.root_after(0, self._update_output_gui, f"Error executing command: {e}", "", is_error=True)

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
        self.root.title("Network Scanner - ONVIF Camera Finder")
        self.root.state('zoomed')

        self.stop_flag = False
        self.search_thread = None
        self.scanning_active = False
        self.found_count = 0
        
        # Bonjour variables
        self.zeroconf = None
        self.bonjour_listener = None
        
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

        # --- Scan Range Management ---
        self.scan_range = {"start_ip": "", "end_ip": ""}
        self.load_settings()
        self.load_camera_data()
        
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
        """Loads application settings, including scan range, from file."""
        if os.path.exists('app_settings.json'):
            try:
                with open('app_settings.json', 'r') as f:
                    settings = json.load(f)
                    if 'scan_range' in settings:
                        self.scan_range = settings['scan_range']
            except json.JSONDecodeError as e:
                self.show_floating_message(f"Error reading app_settings.json: {e}")
            except Exception as e:
                self.show_floating_message(f"Error loading application settings: {e}")

    def save_settings(self):
        """Saves application settings, including scan range, to file."""
        settings = {
            'scan_range': self.scan_range
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
        # Added for duplicate MAC
        self.style.configure('mac_dup.TLabel', background='#ffcc99')

    def create_widgets(self):
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
        
        # Bonjour Scan Button
        self.bonjour_btn = ttk.Button(
            control_frame,
            text="Scan Bonjour",
            command=self.start_bonjour_scan
        )
        self.bonjour_btn.pack(side=tk.LEFT, padx=5)

        # Credential Management Button
        self.manage_creds_btn = ttk.Button(
            control_frame,
            text="Manage Credentials",
            command=self.open_credential_manager
        )
        self.manage_creds_btn.pack(side=tk.LEFT, padx=5)

        # Scan Range Management Button
        self.manage_scan_range_btn = ttk.Button(
            control_frame,
            text="Manage Scan Range",
            command=self.open_scan_range_manager
        )
        self.manage_scan_range_btn.pack(side=tk.LEFT, padx=5)

        # Export to Excel Button
        self.export_excel_btn = ttk.Button(
            control_frame,
            text="Export to Excel",
            command=self.export_to_excel
        )
        self.export_excel_btn.pack(side=tk.LEFT, padx=5)

        # CMD Tools Button (changed from menubutton)
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

        # Results Treeview (REMOVED 'Last Seen' COLUMN)
        tree_frame = ttk.Frame(main_frame)
        tree_frame.pack(fill=tk.BOTH, expand=True)

        columns = ('IP', 'MAC', 'Hostname', 'Credential Set', 'Open Ports', 'RTSP URL', 'Camera Status', 'Snapshot')
        self.tree = ttk.Treeview(tree_frame, columns=columns, show='headings')
        
        col_widths = {
            'IP': 120, 
            'MAC': 130, 
            'Hostname': 150, 
            'Credential Set': 120,
            'Open Ports': 120,
            'RTSP URL': 250,
            'Camera Status': 150,
            'Snapshot': 80
        }
        for col in columns:
            self.tree.heading(col, text=col)
            self.tree.column(col, width=col_widths.get(col, 100))

        scrollbar = ttk.Scrollbar(tree_frame, orient=tk.VERTICAL, command=self.tree.yview)
        self.tree.configure(yscroll=scrollbar.set)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        self.tree.pack(fill=tk.BOTH, expand=True)

        self.tree.tag_configure('ip_dup', background='#ffcccc')
        self.tree.tag_configure('camera_found', background='#ccffcc')
        self.tree.tag_configure('camera_error', background='#ffcccc')
        self.tree.tag_configure('bonjour_device', background='#cce5ff')
        # Added for duplicate MAC
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
            
    def add_bonjour_device(self, ip, port, hostname):
        """Adds a Bonjour device to the table"""
        existing = False
        for child in self.tree.get_children():
            if self.tree.item(child, 'values')[0] == ip:
                existing = True
                break
        
        if not existing:
            device = (
                ip,
                "N/A (Bonjour)",
                hostname,
                "Default Admin",
                str(port),
                "",
                "Bonjour Device",
                "Unavailable"
            )
            item_id = self.tree.insert('', tk.END, values=device, tags=('bonjour_device',))
            self.root.after(0, self.update_status, f"Bonjour device found: {hostname} ({ip})")
            self.onvif_queue.put((ip, item_id))
            self.port_scan_queue.put((ip, item_id))

    def on_right_click(self, event):
        item_id = self.tree.identify_row(event.y)
        column_id = self.tree.identify_column(event.x)

        if not item_id or not column_id:
            return

        col_index = int(column_id.replace('#', '')) - 1
        columns = ('IP', 'MAC', 'Hostname', 'Credential Set', 'Open Ports', 'RTSP URL', 'Camera Status', 'Snapshot')
        column_name = columns[col_index] if 0 <= col_index < len(columns) else None

        if not column_name:
            return

        cell_value = self.tree.item(item_id, 'values')[col_index]

        context_menu = Menu(self.root, tearoff=0)
        context_menu.add_command(label=f"Copy '{cell_value}'", command=lambda: self.copy_to_clipboard(cell_value))
        context_menu.post(event.x_root, event.y_root)

    def copy_to_clipboard(self, text):
        self.root.clipboard_clear()
        self.root.clipboard_append(text)
        self.show_floating_message(f"'{text}' copied to clipboard")

    def export_to_excel(self):
        if not self.tree.get_children():
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

            headers = [self.tree.heading(col)['text'] for col in self.tree['columns']]
            sheet.append(headers)

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
        values = self.tree.item(item, 'values')
        ip = values[0]
        
        selected_cred_set_name = self.cred_set_var.get()
        if not selected_cred_set_name or selected_cred_set_name not in self.credential_sets:
            self.show_floating_message("Please select a valid credential set")
            return

        self.camera_ip_to_cred_set[ip] = selected_cred_set_name
        self.save_camera_data()
            
        new_values = list(values)
        if len(new_values) >= 4:  # Adjusted index after removing Last Seen
            new_values[3] = selected_cred_set_name
            self.tree.item(item, values=new_values)
            self.onvif_queue.put((ip, item))
            self.show_floating_message("Credential set applied")
        else:
            self.show_floating_message("Invalid data structure")

    def on_tree_select(self, event):
        selected = self.tree.selection()
        if selected:
            values = self.tree.item(selected[0], 'values')
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
                    for item_id in self.tree.get_children():
                        if self.tree.item(item_id, 'values')[0] == ip:
                            current_values = list(self.tree.item(item_id, 'values'))
                            current_values[3] = "Default Admin"  # Adjusted index
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
                cred_password_var.set("") 

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
        cmd_window.title("CMD Network Tools")
        self.center_window(cmd_window)
        cmd_window.transient(self.root)
        cmd_window.grab_set()
        cmd_window.geometry("800x600")
        cmd_window.columnconfigure(0, weight=1)
        cmd_window.rowconfigure(0, weight=1)

        main_frame = ttk.Frame(cmd_window, padding="10")
        main_frame.grid(row=0, column=0, sticky="nsew")
        main_frame.columnconfigure(0, weight=1)
        main_frame.rowconfigure(1, weight=1)

        # Command Entry and Execute Button
        cmd_input_frame = ttk.Frame(main_frame)
        cmd_input_frame.grid(row=0, column=0, sticky="ew", pady=5)
        cmd_input_frame.columnconfigure(1, weight=1)

        ttk.Label(cmd_input_frame, text="Command:").grid(row=0, column=0, padx=5, sticky="w")
        self.cmd_entry_var = tk.StringVar()
        cmd_entry = ttk.Entry(cmd_input_frame, textvariable=self.cmd_entry_var, width=80)
        cmd_entry.grid(row=0, column=1, padx=5, sticky="ew")

        execute_button = ttk.Button(
            cmd_input_frame,
            text="Execute",
            command=lambda: self.cmd_executor.execute_command(self.cmd_entry_var.get())
        )
        execute_button.grid(row=0, column=2, padx=5)
        
        # Output Display Area
        output_frame = ttk.LabelFrame(main_frame, text="Command Output", padding="10")
        output_frame.grid(row=1, column=0, sticky="nsew", pady=10)
        output_frame.columnconfigure(0, weight=1)
        output_frame.rowconfigure(0, weight=1)

        self.cmd_output_text = tk.Text(output_frame, wrap=tk.WORD, font=("Consolas", 10))
        self.cmd_output_text.grid(row=0, column=0, sticky="nsew")
        
        output_scrollbar = ttk.Scrollbar(output_frame, orient=tk.VERTICAL, command=self.cmd_output_text.yview)
        self.cmd_output_text.config(yscrollcommand=output_scrollbar.set)
        output_scrollbar.grid(row=0, column=1, sticky="ns")

        self.cmd_output_text.config(state=tk.DISABLED)
        self.cmd_executor = CmdToolExecutor(self.cmd_output_text, self.root.after)

        # Copy to Clipboard Button
        copy_button = ttk.Button(
            output_frame,
            text="Copy Output",
            command=self._copy_cmd_output_from_window
        )
        copy_button.grid(row=1, column=0, pady=5)

        # Notebook for categorized commands
        notebook = ttk.Notebook(main_frame)
        notebook.grid(row=2, column=0, sticky="nsew", pady=10)
        main_frame.rowconfigure(2, weight=1)

        self.network_tab = ttk.Frame(notebook, padding="10")
        self.system_tab = ttk.Frame(notebook, padding="10")

        notebook.add(self.network_tab, text="Network & Troubleshooting")
        notebook.add(self.system_tab, text="System & Processes")

        self._add_network_commands(self.network_tab)
        self._add_system_commands(self.system_tab)

        close_button = ttk.Button(cmd_window, text="Close", command=cmd_window.destroy)
        close_button.grid(row=1, column=0, pady=10)

        cmd_window.protocol("WM_DELETE_WINDOW", cmd_window.destroy)
        cmd_window.wait_window()

    def _add_command_button(self, parent_frame, text, command_str, row, col):
        btn = ttk.Button(parent_frame, text=text, 
                         command=lambda: self.cmd_entry_var.set(command_str))
        btn.grid(row=row, column=col, padx=5, pady=5, sticky="ew")

    def _add_network_commands(self, parent_frame):
        for i in range(3): parent_frame.columnconfigure(i, weight=1)

        ip_config_frame = ttk.LabelFrame(parent_frame, text="IP Configuration")
        ip_config_frame.grid(row=0, column=0, columnspan=3, sticky="ew", padx=5, pady=5)
        for i in range(3): ip_config_frame.columnconfigure(i, weight=1)
        self._add_command_button(ip_config_frame, "ipconfig", "ipconfig", 0, 0)
        self._add_command_button(ip_config_frame, "ipconfig /all", "ipconfig /all", 0, 1)
        self._add_command_button(ip_config_frame, "ipconfig /renew", "ipconfig /renew", 0, 2)
        self._add_command_button(ip_config_frame, "ipconfig /release", "ipconfig /release", 1, 0)

        conn_test_frame = ttk.LabelFrame(parent_frame, text="Connectivity Test")
        conn_test_frame.grid(row=1, column=0, columnspan=3, sticky="ew", padx=5, pady=5)
        for i in range(3): conn_test_frame.columnconfigure(i, weight=1)
        self._add_command_button(conn_test_frame, "ping google.com", "ping google.com -n 4", 0, 0)
        self._add_command_button(conn_test_frame, "ping [IP/Hostname] -t", "ping [Enter IP/Hostname] -t", 0, 1)
        self._add_command_button(conn_test_frame, "tracert google.com", "tracert google.com", 0, 2)
        self._add_command_button(conn_test_frame, "pathping google.com", "pathping google.com", 1, 0)
        self._add_command_button(conn_test_frame, "telnet [IP] [Port]", "telnet [Enter IP] [Enter Port]", 1, 1)

        net_conn_frame = ttk.LabelFrame(parent_frame, text="Network Connections & Ports")
        net_conn_frame.grid(row=2, column=0, columnspan=3, sticky="ew", padx=5, pady=5)
        for i in range(3): net_conn_frame.columnconfigure(i, weight=1)
        self._add_command_button(net_conn_frame, "netstat -an", "netstat -an", 0, 0)
        self._add_command_button(net_conn_frame, "nslookup google.com", "nslookup google.com", 0, 1)
        self._add_command_button(net_conn_frame, "getmac", "getmac", 0, 2)
        self._add_command_button(net_conn_frame, "arp -a", "arp -a", 1, 0)

        net_config_frame = ttk.LabelFrame(parent_frame, text="Network Configuration & Routing")
        net_config_frame.grid(row=3, column=0, columnspan=3, sticky="ew", padx=5, pady=5)
        for i in range(3): net_config_frame.columnconfigure(i, weight=1)
        self._add_command_button(net_config_frame, "netsh (Interactive)", "netsh", 0, 0)
        self._add_command_button(net_config_frame, "route print", "route print", 0, 1)
        self._add_command_button(net_config_frame, "route add...", "route add [destination] mask [netmask] [gateway]", 1, 0)
        self._add_command_button(net_config_frame, "route delete...", "route delete [destination]", 1, 1)

    def _add_system_commands(self, parent_frame):
        for i in range(3): parent_frame.columnconfigure(i, weight=1)

        sys_info_frame = ttk.LabelFrame(parent_frame, text="System Information")
        sys_info_frame.grid(row=0, column=0, columnspan=3, sticky="ew", padx=5, pady=5)
        for i in range(3): sys_info_frame.columnconfigure(i, weight=1)
        self._add_command_button(sys_info_frame, "systeminfo", "systeminfo", 0, 0)
        self._add_command_button(sys_info_frame, "driverquery", "driverquery", 0, 1)
        self._add_command_button(sys_info_frame, "powercfg /energy", "powercfg /energy", 0, 2)

        process_mgmt_frame = ttk.LabelFrame(parent_frame, text="Process & Service Management")
        process_mgmt_frame.grid(row=1, column=0, columnspan=3, sticky="ew", padx=5, pady=5)
        for i in range(3): process_mgmt_frame.columnconfigure(i, weight=1)
        self._add_command_button(process_mgmt_frame, "tasklist", "tasklist", 0, 0)
        self._add_command_button(process_mgmt_frame, "taskkill /F /IM [Name]", "taskkill /F /IM [Enter Image Name]", 0, 1)
        self._add_command_button(process_mgmt_frame, "sc query [Service]", "sc query [Enter Service Name]", 0, 2)
        self._add_command_button(process_mgmt_frame, "sc start [Service]", "sc start [Enter Service Name]", 1, 0)
        self._add_command_button(process_mgmt_frame, "sc stop [Service]", "sc stop [Enter Service Name]", 1, 1)
        self._add_command_button(process_mgmt_frame, "net start [Service]", "net start [Enter Service Name]", 2, 0)
        self._add_command_button(process_mgmt_frame, "net stop [Service]", "net stop [Enter Service Name]", 2, 1)

        event_log_frame = ttk.LabelFrame(parent_frame, text="Event Log & Tracing")
        event_log_frame.grid(row=2, column=0, columnspan=3, sticky="ew", padx=5, pady=5)
        for i in range(3): event_log_frame.columnconfigure(i, weight=1)
        self._add_command_button(event_log_frame, "wevtutil qe System", "wevtutil qe System /c:10 /f:text", 0, 0)
        self._add_command_button(event_log_frame, "logman query", "logman query", 0, 1)

    def _copy_cmd_output_from_window(self):
        output_content = self.cmd_output_text.get(1.0, tk.END).strip()
        if output_content:
            self.root.clipboard_clear()
            self.root.clipboard_append(output_content)
            self.show_floating_message("Command output copied to clipboard")
        else:
            self.show_floating_message("No output to copy")

    def start_search(self):
        if not self.scanning_active:
            self.found_count = 0
            for item in self.tree.get_children():
                self.tree.delete(item)
            self.thumbnail_cache = {}
            self.hover_image_cache = {}
            
            self.progress_bar.pack(side=tk.RIGHT, fill=tk.X, expand=True)
            self.progress_bar['value'] = 0
            
            self.scanning_active = True
            self.stop_flag = False
            self.search_btn['state'] = tk.DISABLED
            self.stop_btn['state'] = tk.NORMAL
            self.update_status("شروع اسکن...")
            self.search_thread = threading.Thread(target=self.scan_network)
            self.search_thread.start()
            self.start_bonjour_scan()

    def stop_search(self):
        self.scanning_active = False
        self.stop_flag = True
        self.search_btn['state'] = tk.NORMAL
        self.stop_btn['state'] = tk.DISABLED
        self.update_status("اسکن متوقف شد.")
        self.progress_bar.pack_forget()
        self.stop_bonjour_scan()

    def update_status(self, message):
        self.progress_label['text'] = message
        self.root.update_idletasks()

    def update_progress(self, value):
        self.progress_bar['value'] = value
        self.root.update_idletasks()

    def get_local_network(self):
        try:
            host_ip = socket.gethostbyname(socket.gethostname())
            network = ipaddress.ip_network(f"{host_ip}/24", strict=False)
            return list(network.hosts())
        except Exception as e:
            self.show_floating_message(f"Error detecting local network: {str(e)}")
            return []

    def get_scan_targets(self):
        start_ip = self.scan_range.get("start_ip")
        end_ip = self.scan_range.get("end_ip")

        if start_ip and end_ip:
            try:
                start_ip_obj = ipaddress.IPv4Address(start_ip)
                end_ip_obj = ipaddress.IPv4Address(end_ip)
                
                if start_ip_obj > end_ip_obj:
                    self.show_floating_message("Invalid IP range - using default")
                    return self.get_local_network()

                targets = []
                current_ip = start_ip_obj
                while current_ip <= end_ip_obj:
                    targets.append(current_ip)
                    current_ip += 1
                return targets
            except ipaddress.AddressValueError:
                self.show_floating_message("Invalid IP format - using default")
                return self.get_local_network()
            except Exception as e:
                self.show_floating_message(f"Error processing range: {e} - using default")
                return self.get_local_network()
        else:
            return self.get_local_network()

    def ip_to_tuple(self, ip_str):
        return tuple(map(int, ip_str.split('.')))

    def scan_network(self):
        try:
            targets = self.get_scan_targets()
            total = len(targets)
            if not total:
                self.update_status("هیچ هدفی برای اسکن وجود ندارد!")
                return

            self.found_count = 0
            self.update_status("در حال اسکن شبکه...")
            
            with concurrent.futures.ThreadPoolExecutor(max_workers=50) as executor:
                futures = {executor.submit(self.scan_ip, str(ip)): ip for ip in targets}
                
                for i, future in enumerate(concurrent.futures.as_completed(futures)):
                    if self.stop_flag:
                        for fut in futures:
                            if not fut.done():
                                fut.cancel()
                        break
                    
                    ip = futures[future]
                    try:
                        result = future.result()
                        if result:
                            ip_str, mac, hostname = result
                            self.found_count += 1
                            
                            if ip_str not in self.camera_ip_to_cred_set:
                                self.camera_ip_to_cred_set[ip_str] = "Default Admin"
                                self.save_camera_data()

                            # Updated device tuple (removed Last Seen)
                            device = (
                                ip_str,
                                mac,
                                hostname,
                                self.camera_ip_to_cred_set.get(ip_str, "Default Admin"),
                                "Scanning...",
                                "",
                                "Searching...",
                                "Unavailable"
                            )
                            self.root.after(0, self.add_device, device)
                    
                    except concurrent.futures.CancelledError:
                        pass
                    except Exception:
                        pass
                    
                    progress = (i + 1) / total * 100
                    self.root.after(0, self.update_progress, progress)
                    self.root.after(0, self.update_status, f"در حال اسکن: {progress:.1f}%")

            self.update_status(f"اسکن شبکه کامل شد. {self.found_count} دستگاه پیدا شد.")
        
        except Exception as e:
            self.show_floating_message(f"Error scanning network: {str(e)}")
        finally:
            self.scanning_active = False
            self.search_btn['state'] = tk.NORMAL
            self.stop_btn['state'] = tk.DISABLED
            self.root.after(2000, self.progress_bar.pack_forget)

    def scan_ip(self, ip_str):
        if self.stop_flag:
            raise concurrent.futures.CancelledError("Scan stopped by user.")
            
        response = ping(ip_str, timeout=0.3)
        if response is not None and response:
            mac, hostname = self.get_device_details(ip_str)
            if mac or hostname:
                return ip_str, mac, hostname
        return None

    def get_device_details(self, ip):
        """
        Gets MAC and hostname. Uses get-mac library for robust MAC address retrieval.
        """
        mac, hostname = "Unknown", "Unknown"
        try:
            # Get MAC address using the reliable get-mac library
            mac_addr = get_mac_address(ip=ip, network_request=True)
            if mac_addr:
                mac = mac_addr.upper()
            else:
                mac = "Unknown"
        except Exception:
            mac = "Error"
        
        try:
            # Get hostname using standard socket library
            hostname = socket.getfqdn(ip)
            if hostname == ip:
                hostname = "Unknown"
        except Exception:
            hostname = "Unknown"

        return mac, hostname

    def get_vendor_from_mac(self, mac):
        """Get vendor name from MAC address using OUI lookup"""
        try:
            # Normalize MAC address
            mac = mac.replace(':', '').replace('-', '').upper()
            oui = mac[:6]
            
            # Lookup OUI in IEEE database (using local mapping)
            # This is a simplified version, in practice you'd use a full OUI database
            vendor_map = {
                '0000C9': 'Cisco',
                '001122': 'Huawei',
                'A0B4A5': 'Samsung',
                '001E06': 'D-Link',
                '001F6B': 'TP-Link',
                'C0AC54': 'Hikvision',
                '0026CD': 'Dahua',
                '001AEF': 'Axis',
                '0090A2': 'Sony',
                '0050F2': 'Dell',
                '001D0F': 'HP',
                '001EC2': 'Apple',
                '001B63': 'Intel',
                '000569': 'Bosch',
                '000DBD': 'Panasonic',
                '001E42': 'Vivotek',
                '001F54': 'Arecont',
                '0021B9': 'Mobotix',
                '0022D2': 'Samsung Techwin',
                '0023F7': 'ACTi',
                '0024F7': 'Sony',
                '0025CB': 'Sony',
                '0026F3': 'Sony',
                '0027F8': 'Sony',
                '0028F8': 'Sony',
                '0029F8': 'Sony',
                '002AF8': 'Sony',
                '002BF8': 'Sony',
                '002CF8': 'Sony',
                '002DF8': 'Sony',
                '002EF8': 'Sony',
                '002FF8': 'Sony',
                '0030F8': 'Sony',
                '0031F8': 'Sony',
                '0032F8': 'Sony',
                '0033F8': 'Sony',
                '0034F8': 'Sony',
                '0035F8': 'Sony',
                '0036F8': 'Sony',
                '0037F8': 'Sony',
                '0038F8': 'Sony',
                '0039F8': 'Sony',
                '003AF8': 'Sony',
                '003BF8': 'Sony',
                '003CF8': 'Sony',
                '003DF8': 'Sony',
                '003EF8': 'Sony',
                '003FF8': 'Sony',
                '0040F8': 'Sony',
                '0041F8': 'Sony',
                '0042F8': 'Sony',
                '0043F8': 'Sony',
                '0044F8': 'Sony',
                '0045F8': 'Sony',
                '0046F8': 'Sony',
                '0047F8': 'Sony',
                '0048F8': 'Sony',
                '0049F8': 'Sony',
                '004AF8': 'Sony',
                '004BF8': 'Sony',
                '004CF8': 'Sony',
                '004DF8': 'Sony',
                '004EF8': 'Sony',
                '004FF8': 'Sony',
                '0050F8': 'Sony',
                '0051F8': 'Sony',
                '0052F8': 'Sony',
                '0053F8': 'Sony',
                '0054F8': 'Sony',
                '0055F8': 'Sony',
                '0056F8': 'Sony',
                '0057F8': 'Sony',
                '0058F8': 'Sony',
                '0059F8': 'Sony',
                '005AF8': 'Sony',
                '005BF8': 'Sony',
                '005CF8': 'Sony',
                '005DF8': 'Sony',
                '005EF8': 'Sony',
                '005FF8': 'Sony',
                '0060F8': 'Sony',
                '0061F8': 'Sony',
                '0062F8': 'Sony',
                '0063F8': 'Sony',
                '0064F8': 'Sony',
                '0065F8': 'Sony',
                '0066F8': 'Sony',
                '0067F8': 'Sony',
                '0068F8': 'Sony',
                '0069F8': 'Sony',
                '006AF8': 'Sony',
                '006BF8': 'Sony',
                '006CF8': 'Sony',
                '006DF8': 'Sony',
                '006EF8': 'Sony',
                '006FF8': 'Sony',
                '0070F8': 'Sony',
                '0071F8': 'Sony',
                '0072F8': 'Sony',
                '0073F8': 'Sony',
                '0074F8': 'Sony',
                '0075F8': 'Sony',
                '0076F8': 'Sony',
                '0077F8': 'Sony',
                '0078F8': 'Sony',
                '0079F8': 'Sony',
                '007AF8': 'Sony',
                '007BF8': 'Sony',
                '007CF8': 'Sony',
                '007DF8': 'Sony',
                '007EF8': 'Sony',
                '007FF8': 'Sony',
                '0080F8': 'Sony',
                '0081F8': 'Sony',
                '0082F8': 'Sony',
                '0083F8': 'Sony',
                '0084F8': 'Sony',
                '0085F8': 'Sony',
                '0086F8': 'Sony',
                '0087F8': 'Sony',
                '0088F8': 'Sony',
                '0089F8': 'Sony',
                '008AF8': 'Sony',
                '008BF8': 'Sony',
                '008CF8': 'Sony',
                '008DF8': 'Sony',
                '008EF8': 'Sony',
                '008FF8': 'Sony',
                '0090F8': 'Sony',
                '0091F8': 'Sony',
                '0092F8': 'Sony',
                '0093F8': 'Sony',
                '0094F8': 'Sony',
                '0095F8': 'Sony',
                '0096F8': 'Sony',
                '0097F8': 'Sony',
                '0098F8': 'Sony',
                '0099F8': 'Sony',
                '009AF8': 'Sony',
                '009BF8': 'Sony',
                '009CF8': 'Sony',
                '009DF8': 'Sony',
                '009EF8': 'Sony',
                '009FF8': 'Sony',
                '00A0F8': 'Sony',
                '00A1F8': 'Sony',
                '00A2F8': 'Sony',
                '00A3F8': 'Sony',
                '00A4F8': 'Sony',
                '00A5F8': 'Sony',
                '00A6F8': 'Sony',
                '00A7F8': 'Sony',
                '00A8F8': 'Sony',
                '00A9F8': 'Sony',
                '00AAF8': 'Sony',
                '00ABF8': 'Sony',
                '00ACF8': 'Sony',
                '00ADF8': 'Sony',
                '00AEF8': 'Sony',
                '00AFF8': 'Sony',
                '00B0F8': 'Sony',
                '00B1F8': 'Sony',
                '00B2F8': 'Sony',
                '00B3F8': 'Sony',
                '00B4F8': 'Sony',
                '00B5F8': 'Sony',
                '00B6F8': 'Sony',
                '00B7F8': 'Sony',
                '00B8F8': 'Sony',
                '00B9F8': 'Sony',
                '00BAF8': 'Sony',
                '00BBF8': 'Sony',
                '00BCF8': 'Sony',
                '00BDF8': 'Sony',
                '00BEF8': 'Sony',
                '00BFF8': 'Sony',
                '00C0F8': 'Sony',
                '00C1F8': 'Sony',
                '00C2F8': 'Sony',
                '00C3F8': 'Sony',
                '00C4F8': 'Sony',
                '00C5F8': 'Sony',
                '00C6F8': 'Sony',
                '00C7F8': 'Sony',
                '00C8F8': 'Sony',
                '00C9F8': 'Sony',
                '00CAF8': 'Sony',
                '00CBF8': 'Sony',
                '00CCF8': 'Sony',
                '00CDF8': 'Sony',
                '00CEF8': 'Sony',
                '00CFF8': 'Sony',
                '00D0F8': 'Sony',
                '00D1F8': 'Sony',
                '00D2F8': 'Sony',
                '00D3F8': 'Sony',
                '00D4F8': 'Sony',
                '00D5F8': 'Sony',
                '00D6F8': 'Sony',
                '00D7F8': 'Sony',
                '00D8F8': 'Sony',
                '00D9F8': 'Sony',
                '00DAF8': 'Sony',
                '00DBF8': 'Sony',
                '00DCF8': 'Sony',
                '00DDF8': 'Sony',
                '00DEF8': 'Sony',
                '00DFF8': 'Sony',
                '00E0F8': 'Sony',
                '00E1F8': 'Sony',
                '00E2F8': 'Sony',
                '00E3F8': 'Sony',
                '00E4F8': 'Sony',
                '00E5F8': 'Sony',
                '00E6F8': 'Sony',
                '00E7F8': 'Sony',
                '00E8F8': 'Sony',
                '00E9F8': 'Sony',
                '00EAF8': 'Sony',
                '00EBF8': 'Sony',
                '00ECF8': 'Sony',
                '00EDF8': 'Sony',
                '00EEF8': 'Sony',
                '00EFF8': 'Sony',
                '00F0F8': 'Sony',
                '00F1F8': 'Sony',
                '00F2F8': 'Sony',
                '00F3F8': 'Sony',
                '00F4F8': 'Sony',
                '00F5F8': 'Sony',
                '00F6F8': 'Sony',
                '00F7F8': 'Sony',
                '00F8F8': 'Sony',
                '00F9F8': 'Sony',
                '00FAF8': 'Sony',
                '00FBF8': 'Sony',
                '00FCF8': 'Sony',
                '00FDF8': 'Sony',
                '00FEF8': 'Sony',
                '00FFF8': 'Sony'
            }
            
            if oui in vendor_map:
                return vendor_map[oui]
        except Exception:
            pass
        return None

    def add_device(self, device):
        ip_tuple = self.ip_to_tuple(device[0])
        
        position = 0
        for child in self.tree.get_children():
            child_ip = self.tree.item(child, 'values')[0]
            child_ip_tuple = self.ip_to_tuple(child_ip)
            if ip_tuple < child_ip_tuple:
                break
            position += 1
        
        item_id = self.tree.insert('', position, values=device)
        self.onvif_queue.put((device[0], item_id))
        self.port_scan_queue.put((device[0], item_id))
        self.highlight_duplicates()

    def update_open_ports(self, item_id, open_ports):
        if self.tree.exists(item_id):
            values = list(self.tree.item(item_id, 'values'))
            ports_str = ', '.join(map(str, open_ports)) if open_ports else "None"
            if len(values) >= 5:  # Adjusted index after removing Last Seen
                values[4] = ports_str
                self.tree.item(item_id, values=values)

    def _update_hover_window_error(self, thread_id, message):
        if thread_id != self.last_hover_thread_id or not self.hover_window:
            return

        if self.hover_image_label:
            self.hover_image_label.config(text=message)
        else:
            error_label = ttk.Label(self.hover_window, text=message)
            error_label.pack(padx=5, pady=5)
        self.hover_window.update_idletasks()
        self.hover_window.wm_geometry(f"+{self.hover_window.winfo_x()}+{self.hover_window.winfo_y()}")

    def update_camera_info(self, item_id, cred_set_name, rtsp_url, camera_status, snapshot_uri):
        if self.tree.exists(item_id):
            values = list(self.tree.item(item_id, 'values'))
            while len(values) < 8:  # Adjusted for removed column
                values.append('')
            
            values[3] = cred_set_name
            values[5] = rtsp_url
            values[6] = camera_status
            
            if camera_status == "Auth Failed":
                values[5] = "رمز و نام کاربری را بررسی کنید"

            snapshot_status_text = "View Image" if snapshot_uri or rtsp_url else "Unavailable"
            values[7] = snapshot_status_text
            
            current_tags = list(self.tree.item(item_id, 'tags'))
            current_tags = [tag for tag in current_tags if not tag.startswith('snapshot_uri:')]
            if snapshot_uri:
                current_tags.append(f'snapshot_uri:{snapshot_uri}')
            
            tags = []
            if "ONVIF Found" in camera_status:
                tags.append('camera_found')
            elif "Error" in camera_status or "Failed" in camera_status:
                tags.append('camera_error')
            
            tags.extend(current_tags)
            
            if snapshot_status_text == "View Image" and self.camera_icon:
                self.tree.item(item_id, values=values, tags=tuple(tags), image=self.camera_icon)
            else:
                self.tree.item(item_id, values=values, tags=tuple(tags), image='')

    def highlight_duplicates(self):
        ip_list = []
        mac_list = []
        
        for child in self.tree.get_children():
            values = self.tree.item(child, 'values')
            ip_list.append(values[0])
            mac_list.append(values[1])
        
        ip_counts = {ip: ip_list.count(ip) for ip in ip_list}
        mac_counts = {}
        for mac in mac_list:
            # Only count valid MAC addresses (ignore "Unknown" and "Error")
            if mac and mac != "Unknown" and mac != "Error" and not mac.startswith("Error:"):
                mac_counts[mac] = mac_counts.get(mac, 0) + 1
        
        for child in self.tree.get_children():
            values = self.tree.item(child, 'values')
            ip, mac = values[0], values[1]
            
            tags = []
            if ip_counts.get(ip, 0) > 1:
                tags.append('ip_dup')
            if mac_counts.get(mac, 0) > 1:
                tags.append('mac_dup')  # Added for duplicate MAC
            
            existing_tags = list(self.tree.item(child, 'tags'))
            for tag in existing_tags:
                if tag.startswith('camera_') or tag.startswith('snapshot_uri:'):
                    tags.append(tag)
            
            self.tree.item(child, tags=tuple(tags))

    def _on_tree_motion(self, event):
        item_id = self.tree.identify_row(event.y)
        column_id = self.tree.identify_column(event.x)

        # Adjusted column index for 'Snapshot' after removing Last Seen
        if item_id and column_id == '#8':
            item_values = self.tree.item(item_id, 'values')
            snapshot_status_text = item_values[7]

            if snapshot_status_text == "View Image":
                if item_id != self.current_hover_item:
                    self._hide_hover_image()
                    self.current_hover_item = item_id

                    ip = item_values[0]
                    rtsp_url = item_values[5] 
                    snapshot_uri = ""
                    # Removed the extra parenthesis causing the SyntaxError
                    item_tags = self.tree.item(item_id, 'tags')
                    for tag in item_tags:
                        if tag.startswith('snapshot_uri:'):
                            snapshot_uri = tag.split(':', 1)[1]
                            break
                    
                    cred_set_name = item_values[3]
                    cred_info = self.credential_sets.get(cred_set_name)
                    username = cred_info['username'] if cred_info else "admin"
                    password = self.decrypt_password(cred_info['password']) if cred_info else "admin"

                    self.hover_window = tk.Toplevel(self.root)
                    self.hover_window.wm_overrideredirect(True)
                    self.hover_window.wm_geometry(f"+{event.x_root + 10}+{event.y_root + 10}")
                    self.hover_window.attributes("-topmost", True)

                    self.hover_image_label = ttk.Label(self.hover_window, text="Loading...")
                    self.hover_image_label.pack(padx=5, pady=5)
                    
                    self.last_hover_thread_id += 1
                    thread_id = self.last_hover_thread_id
                    self.hover_image_thread = threading.Thread(target=self._fetch_thumbnail_for_hover, 
                                                               args=(thread_id, ip, username, password, rtsp_url, snapshot_uri))
                    self.hover_image_thread.daemon = True
                    self.hover_image_thread.start()
            else:
                self._hide_hover_image()
        else:
            self._hide_hover_image()

    def _on_tree_leave(self, event):
        self._hide_hover_image()

    def _hide_hover_image(self):
        if self.hover_window:
            self.hover_window.destroy()
            self.hover_window = None
            self.hover_image_label = None
            self.current_hover_item = None
            self.current_hover_image_tk = None

    def _fetch_thumbnail_for_hover(self, thread_id, ip, username, password, rtsp_url, snapshot_uri):
        if thread_id != self.last_hover_thread_id:
            return

        thumbnail_size = (160, 120)
        image_key = f"hover_thumbnail_{ip}"

        if image_key in self.hover_image_cache:
            self.root.after(0, lambda: self._update_hover_window(thread_id, self.hover_image_cache[image_key]))
            return

        image_data = None
        
        if snapshot_uri:
            try:
                auth = (username, password) if username and password else None
                response = requests.get(snapshot_uri, auth=auth, timeout=3)
                response.raise_for_status()
                image_data = response.content
            except Exception as e:
                image_data = None

        if not image_data and rtsp_url:
            try:
                import cv2
                if username and password:
                    parsed_url = urlparse(rtsp_url)
                    netloc_with_auth = f"{username}:{password}@{parsed_url.hostname}"
                    if parsed_url.port:
                        netloc_with_auth += f":{parsed_url.port}"
                    rtsp_url_with_auth = parsed_url._replace(netloc=netloc_with_auth).geturl()
                else:
                    rtsp_url_with_auth = rtsp_url

                cap = cv2.VideoCapture(rtsp_url_with_auth)
                if not cap.isOpened():
                    raise ConnectionError("Cannot open RTSP stream for thumbnail.")
                
                ret, frame = False, None
                for _ in range(5):
                    ret, frame = cap.read()
                    if not ret:
                        break
                
                cap.release()
                
                if ret and frame is not None:
                    image_pil = Image.fromarray(cv2.cvtColor(frame, cv2.COLOR_BGR2RGB))
                    image_pil.thumbnail(thumbnail_size, Image.LANCZOS)
                    img_byte_arr = io.BytesIO()
                    image_pil.save(img_byte_arr, format='PNG')
                    image_data = img_byte_arr.getvalue()
                else:
                    raise ValueError("Failed to read frame from RTSP stream for thumbnail.")

            except ImportError:
                image_data = None
            except Exception as e:
                image_data = None

        if image_data:
            try:
                img = Image.open(io.BytesIO(image_data))
                img.thumbnail(thumbnail_size, Image.LANCZOS)
                photo = ImageTk.PhotoImage(img)
                self.hover_image_cache[image_key] = photo
                self.root.after(0, lambda: self._update_hover_window(thread_id, photo))
            except Exception as e:
                self.root.after(0, lambda: self._update_hover_window_error(thread_id, "Error loading image"))
        else:
            self.root.after(0, lambda: self._update_hover_window_error(thread_id, "No image available"))

    def _update_hover_window(self, thread_id, photo):
        if thread_id != self.last_hover_thread_id or not self.hover_window:
            return

        if self.hover_image_label:
            self.hover_image_label.destroy()
        
        self.current_hover_image_tk = photo
        image_label = ttk.Label(self.hover_window, image=photo)
        image_label.pack()
        self.hover_window.update_idletasks()
        self.hover_window.wm_geometry(f"+{self.hover_window.winfo_x()}+{self.hover_window.winfo_y()}")

if __name__ == "__main__":
    root = tk.Tk()
    app = RealTimeNetworkScanner(root)
    root.mainloop()
