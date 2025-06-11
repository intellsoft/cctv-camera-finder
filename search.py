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
import openpyxl # For Excel export
import requests # For fetching camera snapshots
from PIL import Image, ImageTk # For image processing and display
import io # Needed for Image.open(io.BytesIO(image_data))
from urllib.parse import urlparse # For parsing RTSP URLs
import webbrowser # For opening web links
import platform # To check operating system

# Global variable for the fixed encryption key (as requested by the user)
# WARNING: Hardcoding the encryption key in the application makes it vulnerable.
# For production environments, consider more secure key management solutions
# (e.g., environment variables, secure key storage, or user-provided keys).
# This key is for demonstration purposes as requested by the user.
FIXED_ENCRYPTION_KEY = b'v8VZkq4W9E7RjTzOYKbLwSdXyGfChN3s1Mn2PpI0Qt6=' 
# You can generate a key like this: Fernet.generate_key()
# Example: b'Abcdefghijklmnopqrstuvwxyz134567890ABCDEF='

class RealTimeNetworkScanner:
    def __init__(self, root):
        self.root = root
        self.root.title("Network Scanner - ONVIF Camera Finder")
        self.root.state('zoomed')

        self.stop_flag = False
        self.search_thread = None
        self.scanning_active = False
        self.found_count = 0
        
        # --- Worker Queues ---
        # Queue for ONVIF discovery tasks
        self.onvif_queue = queue.Queue()
        self.onvif_threads = []
        # Queue for Port Scanning tasks (NEW)
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
        # Stores named sets of credentials: {'set_name': {'username': 'user', 'password': 'encrypted_pass'}}
        self.credential_sets = {} 
        # Stores IP to credential set name mapping: {'ip': 'set_name'}
        self.camera_ip_to_cred_set = {} 

        # Cache for PhotoImage objects to prevent garbage collection
        self.thumbnail_cache = {} 
        self.hover_image_cache = {} # Cache for small hover thumbnails

        # Create a small static image for the Treeview column
        self.camera_icon = None
        try:
            # Create a small placeholder image (e.g., 16x16 pixel green square)
            img = Image.new('RGB', (16, 16), color = 'green')
            self.camera_icon = ImageTk.PhotoImage(img)
        except Exception as e:
            print(f"Could not create camera icon: {e}")
            self.camera_icon = None # Fallback to no icon

        # Hover image related variables
        self.hover_window = None
        self.hover_image_label = None
        self.current_hover_item = None
        self.current_hover_image_tk = None # To prevent GC for the hover image
        self.hover_image_thread = None
        self.last_hover_thread_id = 0 # To ensure only the latest hover request updates the tooltip

        # --- Scan Range Management ---
        self.scan_range = {"start_ip": "", "end_ip": ""} # Stores the user-defined scan range
        self.load_settings() # Load scan range and camera data on startup

        self.load_camera_data() # Load both credential sets and camera mappings
        
        self.create_widgets()
        self.setup_style()
        self.start_worker_threads() # Start all worker threads

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
            return "Decryption Failed" # Return a clear message if decryption fails

    def load_camera_data(self):
        """Loads camera information and credential sets from file."""
        self.credential_sets = {
            "Default Admin": {"username": "admin", "password": self.encrypt_password("admin")}
        } # Default credential set
        self.camera_ip_to_cred_set = {}

        if os.path.exists('camera_data.json'):
            try:
                with open('camera_data.json', 'r') as f:
                    data = json.load(f)
                    if 'credential_sets' in data:
                        # Decrypt passwords when loading
                        for name, creds in data['credential_sets'].items():
                            self.credential_sets[name] = {
                                'username': creds['username'],
                                'password': creds['password'] # Store encrypted in memory
                            }
                    if 'camera_ip_to_cred_set' in data:
                        self.camera_ip_to_cred_set = data['camera_ip_to_cred_set']
            except json.JSONDecodeError as e:
                messagebox.showerror("Error", f"Error reading camera_data.json: {e}\nThe file might be corrupted.")
            except Exception as e:
                messagebox.showerror("Error", f"Error loading camera data: {e}")
        
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
            messagebox.showerror("Error", f"Error saving camera data: {e}")

    def load_settings(self):
        """Loads application settings, including scan range, from file."""
        if os.path.exists('app_settings.json'):
            try:
                with open('app_settings.json', 'r') as f:
                    settings = json.load(f)
                    if 'scan_range' in settings:
                        self.scan_range = settings['scan_range']
            except json.JSONDecodeError as e:
                messagebox.showerror("Error", f"Error reading app_settings.json: {e}\nThe file might be corrupted.")
            except Exception as e:
                messagebox.showerror("Error", f"Error loading application settings: {e}")

    def save_settings(self):
        """Saves application settings, including scan range, to file."""
        settings = {
            'scan_range': self.scan_range
        }
        try:
            with open('app_settings.json', 'w') as f:
                json.dump(settings, f, indent=4)
        except Exception as e:
            messagebox.showerror("Error", f"Error saving application settings: {e}")

    def start_worker_threads(self):
        """Starts all worker threads (ONVIF and Port Scan)."""
        # Start ONVIF worker threads
        for _ in range(10):  # 10 threads for concurrent discovery
            t = threading.Thread(target=self.onvif_worker, daemon=True)
            t.start()
            self.onvif_threads.append(t)
        # Start Port Scan worker threads (NEW)
        for _ in range(20): # 20 threads for concurrent port scanning
            t = threading.Thread(target=self.port_scan_worker, daemon=True)
            t.start()
            self.port_scan_threads.append(t)

    def onvif_worker(self):
        """ONVIF discovery worker. Gets tasks from the onvif_queue."""
        while True:
            ip, item_id = self.onvif_queue.get()
            if self.stop_flag or not self.tree.exists(item_id):
                self.onvif_queue.task_done()
                continue
                
            self.root.after(0, self.update_status, f"Discovering ONVIF for {ip}")
            
            # Get the credential set name associated with this IP
            cred_set_name = self.camera_ip_to_cred_set.get(ip, "Default Admin")
            cred_info = self.credential_sets.get(cred_set_name)

            username = "admin"
            password = "admin"

            if cred_info:
                username = cred_info['username']
                password = self.decrypt_password(cred_info['password']) # Decrypt for use

            # Test camera connection
            camera_status, rtsp_url, snapshot_uri = self.check_onvif_camera(ip, username, password)
            
            # If authentication failed and it wasn't the default set, try with default
            if camera_status == "Auth Failed" and cred_set_name != "Default Admin":
                default_cred_info = self.credential_sets.get("Default Admin")
                if default_cred_info:
                    default_username = default_cred_info['username']
                    default_password = self.decrypt_password(default_cred_info['password'])
                    camera_status, rtsp_url, snapshot_uri = self.check_onvif_camera(ip, default_username, default_password)
                    if camera_status == "ONVIF Found":
                        # If found with default, assign it to this IP
                        self.camera_ip_to_cred_set[ip] = "Default Admin"
                        self.save_camera_data()
                        cred_set_name = "Default Admin" # Update for UI display
            
            # Update the UI
            self.root.after(0, self.update_camera_info, item_id, cred_set_name, rtsp_url, camera_status, snapshot_uri)
            self.onvif_queue.task_done()

    def port_scan_worker(self):
        """
        Port scanning worker. Gets tasks from the port_scan_queue.
        This is a new worker to handle port scanning concurrently.
        """
        while True:
            ip, item_id = self.port_scan_queue.get()
            if self.stop_flag or not self.tree.exists(item_id):
                self.port_scan_queue.task_done()
                continue
            
            common_ports = [80, 443, 554, 8080, 8000, 22, 23, 37777, 8899, 81]
            open_ports = []
            
            # Use a thread pool for scanning ports of a single IP to speed it up
            with concurrent.futures.ThreadPoolExecutor(max_workers=len(common_ports)) as executor:
                future_to_port = {executor.submit(self.scan_single_port, ip, port): port for port in common_ports}
                for future in concurrent.futures.as_completed(future_to_port):
                    port = future_to_port[future]
                    try:
                        if future.result():
                            open_ports.append(port)
                    except Exception:
                        pass # Ignore exceptions from individual port scans
            
            # Sort the found ports
            open_ports.sort()
            
            # Update the UI with the found open ports
            self.root.after(0, self.update_open_ports, item_id, open_ports)
            self.port_scan_queue.task_done()

    def scan_single_port(self, ip, port):
        """Scans a single port on a given IP. Returns True if open, False otherwise."""
        try:
            with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
                s.settimeout(0.5) # Short timeout for faster scanning
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
            # Connect to the camera
            cam = ONVIFCamera(ip, 80, username, password)
            
            # Get media service
            media_service = cam.create_media_service()
            
            # Get profiles
            profiles = media_service.GetProfiles()
            if not profiles:
                return "No Profiles", "", ""
            
            # Get stream link
            token = profiles[0].token
            stream_uri = media_service.GetStreamUri({
                'StreamSetup': {'Stream': 'RTP-Unicast', 'Transport': 'RTSP'},
                'ProfileToken': token
            })
            rtsp_url = stream_uri.Uri

            # Try to get Snapshot URI
            try:
                imaging_service = cam.create_imaging_service()
                snapshot_uri_response = imaging_service.GetSnapshotUri({'ProfileToken': token})
                snapshot_uri = snapshot_uri_response.Uri
            except Exception as e:
                print(f"Error getting Snapshot URI for {ip}: {e}")
                snapshot_uri = ""

            return "ONVIF Found", rtsp_url, snapshot_uri
        except Exception as e:
            # Handle specific error types for clearer status messages
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

        # Camera Credentials Selection Frame (for selected camera)
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
        self.update_cred_combobox_options() # Populate initial options
        
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
        self.progress_bar.pack_forget()  # Initially hidden

        # Results Treeview
        tree_frame = ttk.Frame(main_frame)
        tree_frame.pack(fill=tk.BOTH, expand=True)

        # UPDATED: Added 'Open Ports' column
        columns = ('IP', 'MAC', 'Hostname', 'Last Seen', 'Credential Set', 'Open Ports', 'RTSP URL', 'Camera Status', 'Snapshot')
        self.tree = ttk.Treeview(tree_frame, columns=columns, show='headings')
        
        # Configure columns
        col_widths = {
            'IP': 120, 
            'MAC': 130, 
            'Hostname': 150, 
            'Last Seen': 100,
            'Credential Set': 120,
            'Open Ports': 120, # NEW: Width for Open Ports column
            'RTSP URL': 250,
            'Camera Status': 150,
            'Snapshot': 80
        }
        for col in columns:
            self.tree.heading(col, text=col)
            self.tree.column(col, width=col_widths.get(col, 100))

        # Add scrollbar
        scrollbar = ttk.Scrollbar(tree_frame, orient=tk.VERTICAL, command=self.tree.yview)
        self.tree.configure(yscroll=scrollbar.set)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        self.tree.pack(fill=tk.BOTH, expand=True)

        # Configure tags
        self.tree.tag_configure('ip_dup', background='#ffcccc')
        self.tree.tag_configure('yellow.TFrame', background='#ffffcc')
        self.tree.tag_configure('purple.TFrame', background='#ffccff')
        self.tree.tag_configure('camera_found', background='#ccffcc')
        self.tree.tag_configure('camera_error', background='#ffcccc')
        
        # Bind selection event and right-click
        self.tree.bind('<<TreeviewSelect>>', self.on_tree_select)
        self.tree.bind("<Button-3>", self.on_right_click) # Right-click bind
        self.tree.bind("<Motion>", self._on_tree_motion) # Mouse motion for hover
        self.tree.bind("<Leave>", self._on_tree_leave) # Mouse leave for hover

        # --- Footer Section ---
        footer_frame = ttk.Frame(self.root)
        footer_frame.pack(side=tk.BOTTOM, fill=tk.X, pady=5)

        footer_text_part1 = "برنامه نویس : محمد علی عباسپور    "
        website_text = "intellsoft.ir"
        footer_text_part2 = " (نرم افزار تخصصی دوربین مداربسته)"
        
        # Use a tk.Text widget for the footer to support clickable links
        self.footer_text_widget = tk.Text(
            footer_frame, 
            height=1, 
            wrap="word", 
            font=("Arial", 9),
            bg=self.root.cget('bg'), # Match background of the root window
            relief="flat", # Remove border
            highlightthickness=0, # Remove focus border
            cursor="arrow" # Default cursor
        )
        self.footer_text_widget.pack(side=tk.LEFT, padx=5)
        
        # Insert text parts
        self.footer_text_widget.insert(tk.END, footer_text_part1)
        self.footer_text_widget.insert(tk.END, website_text, "link") # Apply "link" tag to website_text
        self.footer_text_widget.insert(tk.END, footer_text_part2)

        # Configure the "link" tag
        self.footer_text_widget.tag_config("link", foreground="blue", underline=1)
        
        # Bind events to the "link" tag
        self.footer_text_widget.tag_bind("link", "<Button-1>", self._open_website_link)
        self.footer_text_widget.tag_bind("link", "<Enter>", self._on_link_enter)
        self.footer_text_widget.tag_bind("link", "<Leave>", self._on_link_leave)
        
        # Make the text widget read-only
        self.footer_text_widget.config(state="disabled")


    def _open_website_link(self, event):
        """Opens the website link in a web browser."""
        webbrowser.open_new("http://intellsoft.ir") # Ensure it's a valid URL

    def _on_link_enter(self, event):
        """Changes cursor to hand when hovering over the link."""
        self.footer_text_widget.config(cursor="hand2")

    def _on_link_leave(self, event):
        """Changes cursor back to default when leaving the link."""
        self.footer_text_widget.config(cursor="arrow") # Set back to arrow for text widget

    def on_right_click(self, event):
        """Handles right-click event on the Treeview."""
        item_id = self.tree.identify_row(event.y)
        column_id = self.tree.identify_column(event.x)

        if not item_id or not column_id:
            return

        col_index = int(column_id.replace('#', '')) - 1
        # UPDATED: Added 'Open Ports' to columns tuple for right-click context
        columns = ('IP', 'MAC', 'Hostname', 'Last Seen', 'Credential Set', 'Open Ports', 'RTSP URL', 'Camera Status', 'Snapshot')
        column_name = columns[col_index] if 0 <= col_index < len(columns) else None

        if not column_name:
            return

        cell_value = self.tree.item(item_id, 'values')[col_index]

        context_menu = Menu(self.root, tearoff=0)
        context_menu.add_command(label=f"Copy '{cell_value}'", command=lambda: self.copy_to_clipboard(cell_value))
        context_menu.post(event.x_root, event.y_root)

    def copy_to_clipboard(self, text):
        """Copies text to the clipboard."""
        self.root.clipboard_clear()
        self.root.clipboard_append(text)
        messagebox.showinfo("Copied", f"'{text}' copied to clipboard.", parent=self.root)

    def export_to_excel(self):
        """Exports table data to an Excel file."""
        if not self.tree.get_children():
            messagebox.showwarning("Warning", "No data to export.", parent=self.root)
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
            messagebox.showinfo("Success", f"Data successfully saved to '{file_path}'.", parent=self.root)
        except Exception as e:
            messagebox.showerror("Error", f"Error saving Excel file: {e}", parent=self.root)


    def update_cred_combobox_options(self):
        """Updates credential combobox options."""
        self.cred_set_combobox['values'] = list(self.credential_sets.keys())
        if self.cred_set_combobox['values']:
            self.cred_set_var.set(self.cred_set_combobox['values'][0])

    def on_cred_set_selected(self, event):
        """Handles selection of a credential set from the combobox."""
        pass

    def apply_camera_credentials(self):
        """Applies the selected credential set to the selected IP."""
        selected = self.tree.selection()
        if not selected:
            messagebox.showwarning("Warning", "Please select a camera.")
            return
            
        item = selected[0]
        values = self.tree.item(item, 'values')
        ip = values[0]
        
        selected_cred_set_name = self.cred_set_var.get()
        if not selected_cred_set_name or selected_cred_set_name not in self.credential_sets:
            messagebox.showwarning("Warning", "Please select a valid credential set.")
            return

        self.camera_ip_to_cred_set[ip] = selected_cred_set_name
        self.save_camera_data()
            
        new_values = list(values)
        if len(new_values) >= 5:
            new_values[4] = selected_cred_set_name
            self.tree.item(item, values=new_values)
            
            # Restart ONVIF discovery for this camera with new credentials
            self.onvif_queue.put((ip, item))
            messagebox.showinfo("Success", "Credential set saved and re-discovery started.")
        else:
            messagebox.showerror("Error", "Invalid data structure.")

    def on_tree_select(self, event):
        """Handles item selection in the Treeview."""
        selected = self.tree.selection()
        if selected:
            values = self.tree.item(selected[0], 'values')
            ip = values[0]
            associated_cred_set = self.camera_ip_to_cred_set.get(ip, "Default Admin")
            self.cred_set_var.set(associated_cred_set)

    def open_credential_manager(self):
        """Opens the credential management window."""
        cred_manager_window = tk.Toplevel(self.root)
        cred_manager_window.title("Manage Credential Sets")
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
                messagebox.showwarning("Warning", "Set name and username cannot be empty.", parent=cred_manager_window)
                return
            if name in self.credential_sets and name != "Default Admin":
                messagebox.showwarning("Warning", f"Set '{name}' already exists. Use 'Update' button to modify.", parent=cred_manager_window)
                return
            
            encrypted_password = self.encrypt_password(password)
            self.credential_sets[name] = {"username": username, "password": encrypted_password}
            self.save_camera_data()
            update_cred_treeview()
            self.update_cred_combobox_options()
            messagebox.showinfo("Success", f"Credential set '{name}' added.", parent=cred_manager_window)
            cred_name_var.set("")
            cred_username_var.set("")
            cred_password_var.set("")

        def update_cred_set():
            selected = cred_tree.selection()
            if not selected:
                messagebox.showwarning("Warning", "Please select a credential set to update.", parent=cred_manager_window)
                return
            
            old_name = cred_tree.item(selected[0], 'values')[0]
            new_name = cred_name_var.get().strip()
            username = cred_username_var.get().strip()
            password = cred_password_var.get()

            if not new_name or not username:
                messagebox.showwarning("Warning", "Set name and username cannot be empty.", parent=cred_manager_window)
                return
            
            if old_name == "Default Admin" and new_name != "Default Admin":
                 messagebox.showwarning("Warning", "Cannot change the name of 'Default Admin' set.", parent=cred_manager_window)
                 return

            if new_name != old_name and new_name in self.credential_sets:
                messagebox.showwarning("Warning", f"Set '{new_name}' already exists.", parent=cred_manager_window)
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
            messagebox.showinfo("Success", f"Credential set '{old_name}' updated to '{new_name}'.", parent=cred_manager_window)
            cred_name_var.set("")
            cred_username_var.set("")
            cred_password_var.set("")

        def delete_cred_set():
            selected = cred_tree.selection()
            if not selected:
                messagebox.showwarning("Warning", "Please select a credential set to delete.", parent=cred_manager_window)
                return
            
            name_to_delete = cred_tree.item(selected[0], 'values')[0]
            
            if name_to_delete == "Default Admin":
                messagebox.showwarning("Warning", "The 'Default Admin' set cannot be deleted.", parent=cred_manager_window)
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
                            current_values[4] = "Default Admin"
                            self.tree.item(item_id, values=current_values)


            del self.credential_sets[name_to_delete]
            self.save_camera_data()
            update_cred_treeview()
            self.update_cred_combobox_options()
            messagebox.showinfo("Success", f"Credential set '{name_to_delete}' deleted.", parent=cred_manager_window)
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
        """Opens a window to manage the custom scan IP range."""
        range_manager_window = tk.Toplevel(self.root)
        range_manager_window.title("Manage Scan Range")
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
                messagebox.showinfo("Success", "Scan range cleared. Will scan local network.", parent=range_manager_window)
                return

            try:
                start_ip_obj = ipaddress.IPv4Address(start_ip)
                end_ip_obj = ipaddress.IPv4Address(end_ip)

                if start_ip_obj > end_ip_obj:
                    messagebox.showwarning("Warning", "Start IP cannot be greater than End IP.", parent=range_manager_window)
                    return
                
                self.scan_range = {"start_ip": start_ip, "end_ip": end_ip}
                self.save_settings()
                messagebox.showinfo("Success", "Scan range saved successfully.", parent=range_manager_window)
            except ipaddress.AddressValueError:
                messagebox.showerror("Error", "Invalid IP Address format.", parent=range_manager_window)
            except Exception as e:
                messagebox.showerror("Error", f"An error occurred: {e}", parent=range_manager_window)

        ttk.Button(button_frame, text="Save Range", command=save_range).pack(side=tk.LEFT, padx=5, pady=5)
        ttk.Button(button_frame, text="Clear Range", command=lambda: [self.start_ip_var.set(""), self.end_ip_var.set(""), save_range()]).pack(side=tk.LEFT, padx=5, pady=5)
        ttk.Button(button_frame, text="Close", command=range_manager_window.destroy).pack(side=tk.RIGHT, padx=5, pady=5)

        range_manager_window.protocol("WM_DELETE_WINDOW", range_manager_window.destroy)
        range_manager_window.wait_window()

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

    def stop_search(self):
        self.scanning_active = False
        self.stop_flag = True
        self.search_btn['state'] = tk.NORMAL
        self.stop_btn['state'] = tk.DISABLED
        self.update_status("اسکن متوقف شد.")
        self.progress_bar.pack_forget()

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
            messagebox.showerror("Error", f"Error detecting local network: {str(e)}")
            return []

    def get_scan_targets(self):
        start_ip = self.scan_range.get("start_ip")
        end_ip = self.scan_range.get("end_ip")

        if start_ip and end_ip:
            try:
                start_ip_obj = ipaddress.IPv4Address(start_ip)
                end_ip_obj = ipaddress.IPv4Address(end_ip)
                
                if start_ip_obj > end_ip_obj:
                    messagebox.showwarning("Warning", "Start IP is greater than End IP in saved settings. Scanning local network instead.")
                    return self.get_local_network()

                targets = []
                current_ip = start_ip_obj
                while current_ip <= end_ip_obj:
                    targets.append(current_ip)
                    current_ip += 1
                return targets
            except ipaddress.AddressValueError:
                messagebox.showerror("Error", "Invalid IP Address in saved scan range. Scanning local network instead.")
                return self.get_local_network()
            except Exception as e:
                messagebox.showerror("Error", f"Error processing saved scan range: {e}. Scanning local network instead.")
                return self.get_local_network()
        else:
            return self.get_local_network()

    def ip_to_tuple(self, ip_str):
        """Converts IP string to a tuple for sorting."""
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

                            # UPDATED: Added placeholder for 'Open Ports'
                            device = (
                                ip_str,
                                mac,
                                hostname,
                                datetime.now().strftime("%H:%M:%S"),
                                self.camera_ip_to_cred_set.get(ip_str, "Default Admin"),
                                "Scanning...", # Open Ports
                                "",  # RTSP URL
                                "Searching...",  # Camera Status
                                "Unavailable" # Snapshot status
                            )
                            self.root.after(0, self.add_device, device)
                    
                    except Exception as e:
                        pass # Ignore errors from individual IP scans
                    
                    progress = (i + 1) / total * 100
                    self.root.after(0, self.update_progress, progress)
                    self.root.after(0, self.update_status, f"در حال اسکن: {progress:.1f}%")

            self.update_status(f"اسکن شبکه کامل شد. {self.found_count} دستگاه پیدا شد.")
        
        except Exception as e:
            messagebox.showerror("Error", f"Error scanning network: {str(e)}")
        finally:
            self.scanning_active = False
            self.search_btn['state'] = tk.NORMAL
            self.stop_btn['state'] = tk.DISABLED
            self.root.after(2000, self.progress_bar.pack_forget)

    def scan_ip(self, ip_str):
        """Scans a single IP (for parallel execution)."""
        if self.stop_flag:
            return None
            
        response = ping(ip_str, timeout=0.3)
        if response is not None and response:
            mac, hostname = self.get_device_details(ip_str)
            if mac or hostname:
                return ip_str, mac, hostname
        return None

    def get_device_details(self, ip):
        try:
            mac = "Unknown"
            hostname = "Unknown"

            creation_flags = 0
            if platform.system() == "Windows":
                creation_flags = subprocess.CREATE_NO_WINDOW

            try:
                arp_process = subprocess.run(
                    ['arp', '-a', ip],
                    capture_output=True,
                    text=True,
                    check=True,
                    creationflags=creation_flags,
                    timeout=2
                )
                arp_output = arp_process.stdout
                mac_match = re.search(r"([0-9A-Fa-f]{2}[:-]){5}([0-9A-Fa-f]{2})", arp_output)
                mac = mac_match.group(0).lower() if mac_match else "Unknown"
            except (subprocess.CalledProcessError, subprocess.TimeoutExpired, FileNotFoundError) as e:
                print(f"Error running arp for {ip}: {e}")
                mac = "Unknown"

            try:
                hostname = socket.gethostbyaddr(ip)[0]
            except (socket.herror, socket.gaierror):
                hostname = "Unknown"
            
            return mac, hostname
        except Exception as e:
            return "Error", f"Error: {str(e)}"

    def add_device(self, device):
        """
        Adds a device to the table and queues it for ONVIF and Port scanning.
        """
        ip_tuple = self.ip_to_tuple(device[0])
        
        position = 0
        for child in self.tree.get_children():
            child_ip = self.tree.item(child, 'values')[0]
            child_ip_tuple = self.ip_to_tuple(child_ip)
            if ip_tuple < child_ip_tuple:
                break
            position += 1
        
        item_id = self.tree.insert('', position, values=device)
        
        # Queue the device for both ONVIF and Port scanning to run concurrently
        self.onvif_queue.put((device[0], item_id))
        self.port_scan_queue.put((device[0], item_id))
        
        self.highlight_duplicates()

    def update_open_ports(self, item_id, open_ports):
        """
        NEW: Updates the 'Open Ports' column for a specific item in the treeview.
        """
        if self.tree.exists(item_id):
            values = list(self.tree.item(item_id, 'values'))
            
            ports_str = ', '.join(map(str, open_ports)) if open_ports else "None"
            
            if len(values) >= 6: # Ensure column exists
                values[5] = ports_str # Index 5 is 'Open Ports'
                self.tree.item(item_id, values=values)

    def update_camera_info(self, item_id, cred_set_name, rtsp_url, camera_status, snapshot_uri):
        """Updates camera information in the UI, now with adjusted indices."""
        if self.tree.exists(item_id):
            values = list(self.tree.item(item_id, 'values'))
            
            # Ensure we have enough columns (now 9)
            while len(values) < 9:
                values.append('')
            
            # UPDATED: Indices are shifted due to the new 'Open Ports' column
            values[4] = cred_set_name    # Credential Set
            values[6] = rtsp_url         # RTSP URL
            values[7] = camera_status    # Camera Status
            
            # UPDATED: New logic for Auth Failed reminder
            if camera_status == "Auth Failed":
                values[6] = "رمز و نام کاربری را بررسی کنید" # "Check username and password"

            snapshot_status_text = "View Image" if snapshot_uri or rtsp_url else "Unavailable"
            values[8] = snapshot_status_text # Snapshot status
            
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
        mac_counts = {mac: mac_list.count(mac) for mac in mac_list}
        
        for child in self.tree.get_children():
            values = self.tree.item(child, 'values')
            ip, mac = values[0], values[1]
            
            tags = []
            if ip_counts.get(ip, 0) > 1:
                tags.append('ip_dup')
            if mac_counts.get(mac, 0) > 1:
                tags.append('mac_dup')
            
            existing_tags = list(self.tree.item(child, 'tags'))
            for tag in existing_tags:
                if tag.startswith('camera_') or tag.startswith('snapshot_uri:'):
                    tags.append(tag)
            
            self.tree.item(child, tags=tuple(tags))

    def _on_tree_motion(self, event):
        """Handles mouse motion over the Treeview for hover functionality."""
        item_id = self.tree.identify_row(event.y)
        column_id = self.tree.identify_column(event.x)

        # UPDATED: Column index for 'Snapshot' is now #9
        if item_id and column_id == '#9':
            item_values = self.tree.item(item_id, 'values')
            snapshot_status_text = item_values[8]

            if snapshot_status_text == "View Image":
                if item_id != self.current_hover_item:
                    self._hide_hover_image()
                    self.current_hover_item = item_id

                    # UPDATED: Indices for fetching values
                    ip = item_values[0]
                    rtsp_url = item_values[6] 
                    snapshot_uri = ""
                    item_tags = self.tree.item(item_id, 'tags')
                    for tag in item_tags:
                        if tag.startswith('snapshot_uri:'):
                            snapshot_uri = tag.split(':', 1)[1]
                            break
                    
                    cred_set_name = item_values[4]
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
        """Handles mouse leaving the Treeview, hides hover image."""
        self._hide_hover_image()

    def _hide_hover_image(self):
        """Hides and destroys the hover image window."""
        if self.hover_window:
            self.hover_window.destroy()
            self.hover_window = None
            self.hover_image_label = None
            self.current_hover_item = None
            self.current_hover_image_tk = None

    def _fetch_thumbnail_for_hover(self, thread_id, ip, username, password, rtsp_url, snapshot_uri):
        """Fetches and processes a thumbnail for hover display."""
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
                print(f"Error fetching hover thumbnail from Snapshot URI ({snapshot_uri}): {e}")
                image_data = None

        if not image_data and rtsp_url:
            try:
                import cv2 # Import here to provide specific error if not installed
                
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
                print("OpenCV not installed, cannot fetch RTSP thumbnail.")
                image_data = None
            except Exception as e:
                print(f"Error fetching hover thumbnail from RTSP ({rtsp_url}): {e}")
                image_data = None

        if image_data:
            try:
                img = Image.open(io.BytesIO(image_data))
                img.thumbnail(thumbnail_size, Image.LANCZOS)
                photo = ImageTk.PhotoImage(img)
                self.hover_image_cache[image_key] = photo
                self.root.after(0, lambda: self._update_hover_window(thread_id, photo))
            except Exception as e:
                print(f"Error processing image for hover: {e}")
                self.root.after(0, lambda: self._update_hover_window_error(thread_id, "Error loading image"))
        else:
            self.root.after(0, lambda: self._update_hover_window_error(thread_id, "No image available"))

    def _update_hover_window(self, thread_id, photo):
        """Updates the hover window with the thumbnail."""
        if thread_id != self.last_hover_thread_id or not self.hover_window:
            return

        if self.hover_image_label:
            self.hover_image_label.destroy()
        
        self.current_hover_image_tk = photo
        image_label = ttk.Label(self.hover_window, image=photo)
        image_label.pack()
        self.hover_window.update_idletasks()
        self.hover_window.wm_geometry(f"+{self.hover_window.winfo_x()}+{self.hover_window.winfo_y()}")

    def _update_hover_window_error(self, thread_id, message):
        """Updates the hover window with an error message."""
        if thread_id != self.last_hover_thread_id or not self.hover_window:
            return

        if self.hover_image_label:
            self.hover_image_label.config(text=message)
        else:
            error_label = ttk.Label(self.hover_window, text=message)
            error_label.pack(padx=5, pady=5)
        self.hover_window.update_idletasks()
        self.hover_window.wm_geometry(f"+{self.hover_window.winfo_x()}+{self.hover_window.winfo_y()}")


if __name__ == "__main__":
    root = tk.Tk()
    app = RealTimeNetworkScanner(root)
    root.mainloop()
