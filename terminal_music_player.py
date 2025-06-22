"""
TermMusic - A terminal inspired music player with spotify and youtube music integration 
Author: Anirudh Deveram 
Version: 1.0.0 
License: GNU GPL 3.0
"""

import tkinter as tk
from tkinter import ttk, filedialog, messagebox, simpledialog, colorchooser
import os 
import json 
import threading 
import time 
from datetime import timedelta
import sys
from pathlib import Path
import configparser
import webbrowser
import urllib.parse

# Importing external libs
try: 
    import pygame
    PYGAME_AVAILABLE = True
except ImportError: 
    PYGAME_AVAILABLE = False

try: 
    from mutagen import File as MF
    from mutagen.id3 import ID3NoHeaderError 
    MUTAGEN_AVAILABLE = True
except ImportError:
    MUTAGEN_AVAILABLE = False

try:
    import spotipy
    from spotipy.oauth2 import SpotifyOAuth
    SPOTIFY_AVAILABLE = True
except ImportError: 
    SPOTIFY_AVAILABLE = False

try: 
    import requests
    REQUESTS_AVAILABLE = True
except ImportError: 
    REQUESTS_AVAILABLE = False

class TerminalMusicPlayer:
    def __init__(self):
        self.root = tk.Tk()
        self.root.title("TermMusic v1.0")
        self.root.geometry("1200x800")
        self.root.minsize(800, 600)
        self.root.configure(bg="#000000")
        
        # Initialize pygame mixer if available
        if PYGAME_AVAILABLE:
            try:
                pygame.mixer.init()
                self.audio_enabled = True
            except:
                self.audio_enabled = False
        else:
            self.audio_enabled = False
        
        # Application data directory
        self.app_data_dir = Path.home() / '.termmusic' 
        self.app_data_dir.mkdir(exist_ok=True)
        self.config_file = self.app_data_dir / 'config.ini'
        self.auth_file = self.app_data_dir / 'auth.json'

        # Initialize streaming configuration FIRST - BEFORE calling init_streaming_services
        self.spotify_config = {
            "client_id": "",
            "client_secret": "",
            "redirect_uri": "http://localhost:8888/callback"
        }
        
        # Streaming service integration variables
        self.spotify_client = None
        self.spotify_authenticated = False
        self.current_source = "local"  # "local", "spotify", "youtube"

        # Application state variables
        self.music_library = []
        self.filtered_library = []
        self.current_track = None
        self.current_track_index = -1
        self.playing = False
        self.paused = False
        self.volume = 80
        self.position = 0
        self.duration = 0
        self.library_paths = []
        self.active_library_path = None

        # Default color themes
        self.default_themes = {
    "Matrix Green": {
        "bg_primary": "#000000",      # Pure black
        "bg_secondary": "#0a0a0a",    # Very dark
        "text_primary": "#00ff00",    # Bright green
        "text_secondary": "#00aa00",  # Medium green
        "text_muted": "#666666",      # Gray
        "accent": "#ffff00",          # Yellow
        "selection": "#003300",       # Dark green
        "border": "#333333"           # Dark gray
    },
    "Amber Terminal": {
        "bg_primary": "#000000",      # Pure black
        "bg_secondary": "#0a0a0a",    # Very dark
        "text_primary": "#ffb000",    # Bright amber
        "text_secondary": "#cc8800",  # Medium amber
        "text_muted": "#666666",      # Gray
        "accent": "#ff6600",          # Orange accent
        "selection": "#332200",       # Dark amber
        "border": "#444444"           # Dark gray
    },
    "Cyan Blue": {
        "bg_primary": "#000000",      # Pure black
        "bg_secondary": "#0a0a0a",    # Very dark
        "text_primary": "#00ffff",    # Bright cyan
        "text_secondary": "#00cccc",  # Medium cyan
        "text_muted": "#666666",      # Gray
        "accent": "#0088ff",          # Blue accent
        "selection": "#003344",       # Dark cyan
        "border": "#333333"           # Dark gray
    },
    "Purple Haze": {
        "bg_primary": "#000000",      # Pure black
        "bg_secondary": "#0a0a0a",    # Very dark
        "text_primary": "#bb88ff",    # Bright purple
        "text_secondary": "#9966cc",  # Medium purple
        "text_muted": "#666666",      # Gray
        "accent": "#ff88ff",          # Pink accent
        "selection": "#332244",       # Dark purple
        "border": "#333333"           # Dark gray
    },
    "Classic DOS": {
        "bg_primary": "#000000",      # Pure black
        "bg_secondary": "#0a0a0a",    # Very dark
        "text_primary": "#ffff00",    # Bright yellow
        "text_secondary": "#cccc00",  # Medium yellow
        "text_muted": "#aaaaaa",      # Light gray
        "accent": "#ffffff",          # White accent
        "selection": "#333300",       # Dark yellow
        "border": "#333333"           # Dark gray
    },
    "Dark Console": {
        "bg_primary": "#000000",      # Pure black
        "bg_secondary": "#0a0a0a",    # Very dark
        "text_primary": "#dcdcdc",    # Light gray
        "text_secondary": "#9cdcfe",  # Light blue
        "text_muted": "#808080",      # Medium gray
        "accent": "#4fc1ff",          # Bright blue
        "selection": "#264f78",       # Dark blue
        "border": "#333333"           # Dark gray
    }
}
        
        # Custom themes directory
        self.themes_dir = self.app_data_dir / 'themes'
        self.themes_dir.mkdir(exist_ok=True)
        self.themes = self.default_themes.copy()
        
        # Column configuration
        self.columns = {
            "track": {"name": "Track", "width": 60, "visible": True},
            "title": {"name": "Title", "width": 300, "visible": True},
            "artist": {"name": "Artist", "width": 200, "visible": True},
            "album": {"name": "Album", "width": 250, "visible": True},
            "time": {"name": "Duration", "width": 80, "visible": True},
            "year": {"name": "Year", "width": 60, "visible": False},
            "genre": {"name": "Genre", "width": 100, "visible": False},
            "bitrate": {"name": "Bitrate", "width": 80, "visible": False},
            "path": {"name": "Path", "width": 400, "visible": False}
        }

        # NOW load configurations and initialize services - AFTER spotify_config is set
        self.load_custom_themes()
        self.load_config()
        self.load_auth_config()
        self.init_streaming_services()

        # Check if first run and show setup
        if self.is_first_run():
            if self.show_initial_setup():
                self.setup_ui()
                self.load_selected_library()
                self.apply_theme()
                self.setup_keybindings()
            else:
                self.root.destroy()
                return
        else:
            self.setup_ui()
            self.load_selected_library()
            self.apply_theme()
            self.setup_keybindings()
        
        # Start the update thread
        self.update_thread = threading.Thread(target=self.update_loop, daemon=True)
        self.update_thread.start()
        
        # Handle window closing
        self.root.protocol("WM_DELETE_WINDOW", self.on_closing)
    
    def load_config(self):
        """Load configuration from file"""
        self.config = configparser.ConfigParser()
        if self.config_file.exists():
            self.config.read(self.config_file)
            self.current_theme = self.config.get('appearance', 'theme', fallback='Matrix Green')
            self.volume = self.config.getint('audio', 'volume', fallback=80)

            # Load visible columns
            for col_id in self.columns: 
                if self.config.has_option('columns', col_id):
                    self.columns[col_id]['visible'] = self.config.getboolean('columns', col_id)

            # Load library paths
            if self.config.has_section('library'):
                paths_str = self.config.get('library', 'paths', fallback='')
                if paths_str:
                    self.library_paths = [p.strip() for p in paths_str.split(';') if p.strip()]
                self.active_library_path = self.config.get('library', 'active_path', fallback=None)
        else:
            self.current_theme = "Matrix Green"
    
    def load_auth_config(self):
        """Load authentication configuration from auth.json"""
        try:
            if self.auth_file.exists():
                with open(self.auth_file, 'r') as f:
                    auth_data = json.load(f)
                
                # Load Spotify credentials
                if 'spotify' in auth_data:
                    spotify_auth = auth_data['spotify']
                    self.spotify_config.update({
                        'client_id': spotify_auth.get('client_id', ''),
                        'client_secret': spotify_auth.get('client_secret', ''),
                        'redirect_uri': spotify_auth.get('redirect_uri', 'http://localhost:8888/callback')
                    })
                    print("Loaded Spotify credentials from auth.json")
                
        except Exception as e:
            print(f"Error loading auth.json: {e}")
            self.create_sample_auth_file()
    
    def create_sample_auth_file(self):
        """Create a sample auth.json file for users"""
        sample_auth = {
            "spotify": {
                "client_id": "your_spotify_client_id_here",
                "client_secret": "your_spotify_client_secret_here",
                "redirect_uri": "http://localhost:8888/callback"
            },
            "_instructions": {
                "spotify_setup": [
                    "1. Go to https://developer.spotify.com/dashboard/applications",
                    "2. Create a new application",
                    "3. Set redirect URI to: http://localhost:8888/callback", 
                    "4. Copy Client ID and Client Secret above",
                    "5. Restart TermMusic"
                ]
            }
        }
        
        try:
            with open(self.auth_file, 'w') as f:
                json.dump(sample_auth, f, indent=4)
            print(f"Created sample auth.json at: {self.auth_file}")
        except Exception as e:
            print(f"Could not create sample auth.json: {e}")
    
    def init_streaming_services(self):
        """Initialize streaming service connections"""
        if SPOTIFY_AVAILABLE and self.spotify_config['client_id'] and self.spotify_config['client_secret']:
            try:
                scope = "user-read-playback-state user-modify-playback-state user-read-currently-playing playlist-read-private playlist-read-collaborative"
                self.spotify_client = spotipy.Spotify(auth_manager=SpotifyOAuth(
                    client_id=self.spotify_config['client_id'],
                    client_secret=self.spotify_config['client_secret'],
                    redirect_uri=self.spotify_config['redirect_uri'],
                    scope=scope,
                    cache_path=str(self.app_data_dir / '.spotify_cache')
                ))
                
                # Test connection
                user = self.spotify_client.current_user()
                if user:
                    self.spotify_authenticated = True
                    print(f"Spotify authenticated as: {user['display_name']}")
                    
            except Exception as e:
                print(f"Spotify authentication failed: {e}")
                self.spotify_authenticated = False
        else:
            self.spotify_authenticated = False
    
    def save_config(self):
        """Save configuration to file"""
        if not self.config.has_section('appearance'):
            self.config.add_section('appearance')
        if not self.config.has_section('audio'):
            self.config.add_section('audio')
        if not self.config.has_section('columns'):
            self.config.add_section('columns')
        if not self.config.has_section('library'):
            self.config.add_section('library')
        
        self.config.set('appearance', 'theme', self.current_theme)
        self.config.set('audio', 'volume', str(self.volume))
        
        for col_id, col_info in self.columns.items():
            self.config.set('columns', col_id, str(col_info['visible']))
        
        # Save library paths
        paths_str = ';'.join(self.library_paths) if self.library_paths else ''
        self.config.set('library', 'paths', paths_str)
        self.config.set('library', 'active_path', self.active_library_path or '')
        
        with open(self.config_file, 'w') as f:
            self.config.write(f)
    
    def is_first_run(self):
        """Check if this is the first run"""
        return not self.library_paths
    
    def load_custom_themes(self):
        """Load custom themes from JSON files"""
        try:
            for theme_file in self.themes_dir.glob('*.json'):
                try:
                    with open(theme_file, 'r') as f:
                        theme_data = json.load(f)
                    
                    required_keys = ['bg_primary', 'bg_secondary', 'text_primary', 'text_secondary', 'text_muted', 'accent', 'selection', 'border']
                    if all(key in theme_data for key in required_keys):
                        theme_name = theme_file.stem
                        self.themes[theme_name] = theme_data
                        print(f"Loaded custom theme: {theme_name}")
                        
                except json.JSONDecodeError:
                    print(f"Invalid JSON in theme file: {theme_file.name}")
                except Exception as e:
                    print(f"Error loading theme {theme_file.name}: {e}")
                    
        except Exception as e:
            print(f"Error loading custom themes: {e}")
    
    def show_initial_setup(self):
        """Show initial setup window for first-time users"""
        setup_window = tk.Toplevel()
        setup_window.title("TermMusic - Initial Setup")
        setup_window.geometry("600x500")
        setup_window.configure(bg='#0a0a0a')
        setup_window.resizable(False, False)
        
        # Center the window
        setup_window.update_idletasks()
        x = (setup_window.winfo_screenwidth() // 2) - (300)
        y = (setup_window.winfo_screenheight() // 2) - (250)
        setup_window.geometry(f"600x500+{x}+{y}")
        
        # Make it modal
        setup_window.transient(self.root)
        setup_window.grab_set()
        self.root.withdraw()
        
        setup_completed = False
        
        # Main frame
        main_frame = tk.Frame(setup_window, bg='#0a0a0a')
        main_frame.pack(fill=tk.BOTH, expand=True, padx=30, pady=30)
        
        # Title
        title_label = tk.Label(main_frame, text="♪ Welcome to TermMusic", 
                              font=("Consolas", 16, "bold"), bg='#0a0a0a', fg='#ffff00')
        title_label.pack(pady=(0, 10))
        
        subtitle_label = tk.Label(main_frame, text="Let's set up your music library", 
                                 font=("Consolas", 12), bg='#0a0a0a', fg='#00aa00')
        subtitle_label.pack(pady=(0, 30))
        
        # Music folders section
        folders_frame = tk.LabelFrame(main_frame, text="Music Folders", 
                                     font=("Consolas", 10, "bold"),
                                     bg='#0a0a0a', fg='#00ff00')
        folders_frame.pack(fill=tk.BOTH, expand=True, pady=(0, 20))
        
        # Folder list
        list_frame = tk.Frame(folders_frame, bg='#0a0a0a')
        list_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        setup_folders = []
        
        folder_listbox = tk.Listbox(list_frame, font=("Consolas", 9),
                                   bg='#1a1a1a', fg='#00ff00',
                                   selectbackground='#003300', height=8)
        folder_listbox.pack(fill=tk.BOTH, expand=True)
        
        # Folder buttons
        button_frame = tk.Frame(list_frame, bg='#0a0a0a')
        button_frame.pack(fill=tk.X, pady=(10, 0))
        
        def add_folder():
            folder = filedialog.askdirectory(title="Select Music Folder", parent=setup_window)
            if folder and folder not in setup_folders:
                setup_folders.append(folder)
                folder_listbox.insert(tk.END, folder)
        
        def remove_folder():
            selection = folder_listbox.curselection()
            if selection:
                index = selection[0]
                folder_listbox.delete(index)
                setup_folders.pop(index)
        
        tk.Button(button_frame, text="Add Folder", font=("Consolas", 9),
                 command=add_folder, bg='#1a1a1a', fg='#00ff00').pack(side=tk.LEFT, padx=(0, 5))
        
        tk.Button(button_frame, text="Remove", font=("Consolas", 9),
                 command=remove_folder, bg='#1a1a1a', fg='#ff6666').pack(side=tk.RIGHT)
        
        # Bottom buttons
        bottom_frame = tk.Frame(main_frame, bg='#0a0a0a')
        bottom_frame.pack(fill=tk.X)
        
        def complete_setup():
            nonlocal setup_completed
            if not setup_folders:
                if messagebox.askyesno("No Folders", 
                                     "Continue without adding music folders?\n\nYou can add them later.", 
                                     parent=setup_window):
                    setup_completed = True
                    setup_window.destroy()
            else:
                self.library_paths = setup_folders
                self.active_library_path = setup_folders[0] if setup_folders else None
                self.save_config()
                setup_completed = True
                setup_window.destroy()
        
        def skip_setup():
            nonlocal setup_completed
            if messagebox.askyesno("Skip Setup", 
                                 "Skip initial setup?", 
                                 parent=setup_window):
                setup_completed = True
                setup_window.destroy()
        
        tk.Button(bottom_frame, text="Skip for Now", font=("Consolas", 10),
                 command=skip_setup, bg='#333333', fg='#cccccc').pack(side=tk.LEFT)
        
        tk.Button(bottom_frame, text="Complete Setup", font=("Consolas", 10),
                 command=complete_setup, bg='#1a1a1a', fg='#ffff00').pack(side=tk.RIGHT)
        
        def on_setup_close():
            nonlocal setup_completed
            setup_completed = False
            setup_window.destroy()
        
        setup_window.protocol("WM_DELETE_WINDOW", on_setup_close)
        setup_window.wait_window()
        self.root.deiconify()
        
        return setup_completed
    
    def setup_ui(self):
        """Setup the user interface"""
        # Main container
        main_frame = tk.Frame(self.root, bg='#0a0a0a')
        main_frame.pack(fill=tk.BOTH, expand=True)
        
        # Header
        self.setup_header(main_frame)
        
        # Track listing
        self.setup_track_listing(main_frame)
        
        # Player controls
        self.setup_player_controls(main_frame)
        
        # Status bar
        self.setup_status_bar(main_frame)
    
    def setup_header(self, parent):
        """Setup header with title and controls"""
        header_frame = tk.Frame(parent, bg='#1a1a1a', height=60)
        header_frame.pack(fill=tk.X)
        header_frame.pack_propagate(False)
        
        # Title
        title_label = tk.Label(header_frame, text="♪ TERMMUSIC v1.0", 
                              font=("Consolas", 14, "bold"), bg='#1a1a1a', fg='#ffff00')
        title_label.pack(side=tk.LEFT, padx=20, pady=15)
        
        # Controls frame
        controls_frame = tk.Frame(header_frame, bg='#1a1a1a')
        controls_frame.pack(side=tk.RIGHT, padx=20, pady=10)
        
        # Theme selector
        tk.Label(controls_frame, text="Theme:", font=("Consolas", 9), 
                bg='#1a1a1a', fg='#00ff00').pack(side=tk.LEFT, padx=(0, 5))
        
        self.theme_var = tk.StringVar(value=self.current_theme)
        self.theme_combo = ttk.Combobox(controls_frame, textvariable=self.theme_var, 
                                       values=list(self.themes.keys()), width=15, state="readonly",
                                       font=("Consolas", 8))
        self.theme_combo.pack(side=tk.LEFT, padx=(0, 10))
        self.theme_combo.bind('<<ComboboxSelected>>', self.change_theme)
        
        # Buttons
        self.create_header_button(controls_frame, "Add Folder", self.add_music_folder)
        self.create_header_button(controls_frame, "Settings", self.show_settings)
    
    def create_header_button(self, parent, text, command):
        """Create a header button"""
        btn = tk.Button(parent, text=text, font=("Consolas", 9), 
                       command=command, relief=tk.RAISED, bd=1,
                       padx=10, pady=2, bg='#333333', fg='#00ff00')
        btn.pack(side=tk.LEFT, padx=(0, 5))
        return btn
    
    def setup_track_listing(self, parent):
        """Setup the main track listing area"""
        # Info frame
        info_frame = tk.Frame(parent, bg='#1a1a1a', height=40)
        info_frame.pack(fill=tk.X)
        info_frame.pack_propagate(False)
        
        self.playlist_info_label = tk.Label(info_frame, text="Library (0 tracks)", 
                                           font=("Consolas", 10, "bold"), bg='#1a1a1a', fg='#ffff00')
        self.playlist_info_label.pack(side=tk.LEFT, padx=15, pady=10)
        
        # Search box
        search_frame = tk.Frame(info_frame, bg='#1a1a1a')
        search_frame.pack(side=tk.RIGHT, padx=15, pady=8)
        
        tk.Label(search_frame, text="Search:", font=("Consolas", 9), 
                bg='#1a1a1a', fg='#00ff00').pack(side=tk.LEFT, padx=(0, 5))
        
        self.search_var = tk.StringVar()
        search_entry = tk.Entry(search_frame, textvariable=self.search_var, font=("Consolas", 9),
                               bg='#333333', fg='#ffffff', width=20, relief=tk.FLAT)
        search_entry.pack(side=tk.LEFT)
        self.search_var.trace('w', self.on_search_change)
        
        # Frame for treeview
        tree_frame = tk.Frame(parent, bg='#0a0a0a')
        tree_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=5)
        
        # Create treeview
        visible_cols = [col_id for col_id, col_info in self.columns.items() if col_info["visible"]]
        self.tree = ttk.Treeview(tree_frame, columns=visible_cols, show='headings', height=15)
        
        # Configure columns
        for col_id in visible_cols:
            col_info = self.columns[col_id]
            self.tree.heading(col_id, text=col_info["name"], anchor=tk.W)
            anchor = tk.E if col_id in ["time", "track", "year", "bitrate"] else tk.W
            self.tree.column(col_id, width=col_info["width"], anchor=anchor, minwidth=50)
        
        # Scrollbars
        v_scrollbar = ttk.Scrollbar(tree_frame, orient=tk.VERTICAL, command=self.tree.yview)
        self.tree.configure(yscrollcommand=v_scrollbar.set)
        
        # Pack everything
        self.tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        v_scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        
        # Bind events
        self.tree.bind('<Double-1>', self.on_track_double_click)
        self.tree.bind('<Return>', self.on_track_enter)
    
    def setup_player_controls(self, parent):
        """Setup player control buttons"""
        controls_frame = tk.Frame(parent, bg='#1a1a1a', height=60)
        controls_frame.pack(fill=tk.X, padx=10, pady=5)
        controls_frame.pack_propagate(False)
        
        # Center the controls
        center_frame = tk.Frame(controls_frame, bg='#1a1a1a')
        center_frame.pack(expand=True)
        
        # Control buttons
        self.prev_btn = self.create_control_button(center_frame, "⏮", self.previous_track)
        self.play_btn = self.create_control_button(center_frame, "▶", self.toggle_playback)
        self.next_btn = self.create_control_button(center_frame, "⏭", self.next_track)
        self.stop_btn = self.create_control_button(center_frame, "⏹", self.stop_playback)
        
        # Now playing
        self.now_playing_label = tk.Label(controls_frame, text="♪ Ready", 
                                         font=("Consolas", 10), bg='#1a1a1a', fg='#ffff00')
        self.now_playing_label.pack(side=tk.LEFT, padx=20)
        
        # Volume control
        vol_frame = tk.Frame(controls_frame, bg='#1a1a1a')
        vol_frame.pack(side=tk.RIGHT, padx=20)
        
        tk.Label(vol_frame, text="Vol:", font=("Consolas", 9), 
                bg='#1a1a1a', fg='#00ff00').pack(side=tk.LEFT)
        
        self.volume_var = tk.IntVar(value=self.volume)
        self.volume_scale = tk.Scale(vol_frame, from_=0, to=100, orient=tk.HORIZONTAL, 
                                    length=100, variable=self.volume_var,
                                    command=self.change_volume, bg='#1a1a1a', fg='#00ff00',
                                    troughcolor='#333333', highlightthickness=0,
                                    font=("Consolas", 8))
        self.volume_scale.pack(side=tk.LEFT, padx=5)
        
        self.volume_label = tk.Label(vol_frame, text=f"{self.volume}%", 
                                    font=("Consolas", 9), bg='#1a1a1a', fg='#00ff00')
        self.volume_label.pack(side=tk.LEFT, padx=5)
    
    def create_control_button(self, parent, text, command):
        """Create a player control button"""
        btn = tk.Button(parent, text=text, font=("Consolas", 14), 
                       command=command, relief=tk.RAISED, bd=2,
                       width=3, height=1, bg='#333333', fg='#00ff00')
        btn.pack(side=tk.LEFT, padx=3)
        return btn
    
    def setup_status_bar(self, parent):
        """Setup status bar"""
        status_frame = tk.Frame(parent, bg='#2a2a2a', height=25)
        status_frame.pack(fill=tk.X)
        status_frame.pack_propagate(False)
        
        self.status_label = tk.Label(status_frame, 
                                    text="Ready | Audio: " + ("Enabled" if self.audio_enabled else "Disabled") + " | F11: Fullscreen | Space: Play/Pause", 
                                    font=("Consolas", 9), bg='#2a2a2a', fg='#888888', anchor=tk.W)
        self.status_label.pack(fill=tk.X, padx=10, pady=3)
    
    def load_selected_library(self):
        """Load the selected music library"""
        if self.active_library_path and os.path.exists(self.active_library_path):
            self.scan_folder(self.active_library_path)
        elif self.library_paths:
            for path in self.library_paths:
                if os.path.exists(path):
                    self.active_library_path = path
                    self.scan_folder(path)
                    break
        else:
            self.load_sample_data()
    
    def load_sample_data(self):
        """Load sample music data for demonstration"""
        sample_tracks = [
            {"track": "01", "title": "Terminal Blues", "artist": "Code Monkeys", "album": "Digital Dreams", "time": "3:45", "year": "2024", "genre": "Electronic", "bitrate": "320", "path": "sample/terminal_blues.mp3"},
            {"track": "02", "title": "Matrix Rain", "artist": "Cyber Collective", "album": "Green Screen", "time": "4:12", "year": "2024", "genre": "Synthwave", "bitrate": "320", "path": "sample/matrix_rain.mp3"},
            {"track": "03", "title": "Command Line Love", "artist": "Terminal Romance", "album": "Console Sessions", "time": "2:58", "year": "2024", "genre": "Chiptune", "bitrate": "320", "path": "sample/command_line_love.mp3"},
            {"track": "04", "title": "Digital Heartbeat", "artist": "Binary Poets", "album": "Algorithmic Soul", "time": "4:33", "year": "2024", "genre": "Electronic", "bitrate": "320", "path": "sample/digital_heartbeat.mp3"}
        ]
        
        self.music_library = sample_tracks
        self.filtered_library = sample_tracks.copy()
        self.update_track_display()
        self.update_playlist_info()
    
    def scan_folder(self, folder_path):
        """Scan a folder for music files"""
        if not os.path.exists(folder_path):
            return
            
        supported_formats = {'.mp3', '.flac', '.ogg', '.m4a', '.wav'}
        tracks = []
        
        try:
            for root, dirs, files in os.walk(folder_path):
                for file in files:
                    if any(file.lower().endswith(ext) for ext in supported_formats):
                        file_path = os.path.join(root, file)
                        track_info = self.extract_metadata(file_path)
                        if track_info:
                            tracks.append(track_info)
            
            self.music_library = tracks
            self.filtered_library = tracks.copy()
            self.update_track_display()
            self.update_playlist_info()
            
        except Exception as e:
            print(f"Error scanning folder {folder_path}: {e}")
    
    def extract_metadata(self, file_path):
        """Extract metadata from audio file"""
        try:
            file_name = os.path.basename(file_path)
            
            # Basic info from filename
            track_info = {
                "track": "",
                "title": os.path.splitext(file_name)[0],
                "artist": "Unknown Artist",
                "album": "Unknown Album",
                "time": "0:00",
                "year": "",
                "genre": "",
                "bitrate": "",
                "path": file_path
            }
            
            # Try to extract metadata if mutagen is available
            if MUTAGEN_AVAILABLE:
                try:
                    audio_file = MF(file_path)
                    if audio_file is not None:
                        # Get duration
                        if hasattr(audio_file, 'info') and audio_file.info.length:
                            duration = int(audio_file.info.length)
                            track_info["time"] = str(timedelta(seconds=duration))[2:7]  # MM:SS format
                        
                        # Get metadata
                        if audio_file.tags:
                            track_info["title"] = str(audio_file.tags.get('TIT2', [file_name])[0]) if 'TIT2' in audio_file.tags else str(audio_file.tags.get('TITLE', [file_name])[0]) if 'TITLE' in audio_file.tags else file_name
                            track_info["artist"] = str(audio_file.tags.get('TPE1', ['Unknown Artist'])[0]) if 'TPE1' in audio_file.tags else str(audio_file.tags.get('ARTIST', ['Unknown Artist'])[0]) if 'ARTIST' in audio_file.tags else "Unknown Artist"
                            track_info["album"] = str(audio_file.tags.get('TALB', ['Unknown Album'])[0]) if 'TALB' in audio_file.tags else str(audio_file.tags.get('ALBUM', ['Unknown Album'])[0]) if 'ALBUM' in audio_file.tags else "Unknown Album"
                            track_info["year"] = str(audio_file.tags.get('TDRC', [''])[0]) if 'TDRC' in audio_file.tags else str(audio_file.tags.get('DATE', [''])[0]) if 'DATE' in audio_file.tags else ""
                            track_info["genre"] = str(audio_file.tags.get('TCON', [''])[0]) if 'TCON' in audio_file.tags else str(audio_file.tags.get('GENRE', [''])[0]) if 'GENRE' in audio_file.tags else ""
                            track_info["track"] = str(audio_file.tags.get('TRCK', [''])[0]) if 'TRCK' in audio_file.tags else str(audio_file.tags.get('TRACKNUMBER', [''])[0]) if 'TRACKNUMBER' in audio_file.tags else ""
                        
                        # Get bitrate
                        if hasattr(audio_file, 'info') and hasattr(audio_file.info, 'bitrate'):
                            track_info["bitrate"] = str(audio_file.info.bitrate)
                            
                except Exception as e:
                    print(f"Error extracting metadata from {file_path}: {e}")
            
            return track_info
            
        except Exception as e:
            print(f"Error processing file {file_path}: {e}")
            return None
    
    def update_track_display(self):
        """Update the track display in the treeview"""
        # Clear existing items
        for item in self.tree.get_children():
            self.tree.delete(item)
        
        # Add tracks
        visible_cols = [col_id for col_id, col_info in self.columns.items() if col_info["visible"]]
        
        for i, track in enumerate(self.filtered_library):
            values = [track.get(col_id, "") for col_id in visible_cols]
            item = self.tree.insert("", "end", values=values)
            
            # Highlight currently playing track
            if self.current_track and track.get("path") == self.current_track.get("path"):
                self.tree.selection_set(item)
                self.current_track_index = i
    
    def update_playlist_info(self):
        """Update playlist information label"""
        track_count = len(self.filtered_library)
        if track_count > 0:
            total_duration = 0
            for track in self.filtered_library:
                time_str = track.get("time", "0:00")
                if ":" in time_str:
                    try:
                        minutes, seconds = map(int, time_str.split(":"))
                        total_duration += minutes * 60 + seconds
                    except:
                        pass
            
            total_time_str = str(timedelta(seconds=total_duration))[2:7] if total_duration < 3600 else str(timedelta(seconds=total_duration))
            self.playlist_info_label.config(text=f"Library ({track_count} tracks, {total_time_str})")
        else:
            self.playlist_info_label.config(text="Library (0 tracks)")
    
    def on_search_change(self, *args):
        """Handle search input changes"""
        search_term = self.search_var.get().lower()
        
        if not search_term:
            self.filtered_library = self.music_library.copy()
        else:
            self.filtered_library = [
                track for track in self.music_library
                if search_term in track.get("title", "").lower() or
                   search_term in track.get("artist", "").lower() or
                   search_term in track.get("album", "").lower()
            ]
        
        self.update_track_display()
        self.update_playlist_info()
    
    def on_track_double_click(self, event):
        """Handle double-click on track"""
        selection = self.tree.selection()
        if selection:
            self.play_selected_track()
    
    def on_track_enter(self, event):
        """Handle Enter key on track"""
        self.play_selected_track()
    
    def play_selected_track(self):
        """Play the currently selected track"""
        selection = self.tree.selection()
        if not selection:
            return
        
        item = selection[0]
        item_index = self.tree.index(item)
        
        if 0 <= item_index < len(self.filtered_library):
            track = self.filtered_library[item_index]
            self.play_track(track)
            self.current_track_index = item_index
    
    def play_track(self, track):
        """Play a specific track"""
        if not track:
            return
        
        self.current_track = track
        track_path = track.get("path", "")
        
        # Update UI
        artist = track.get("artist", "Unknown Artist")
        title = track.get("title", "Unknown Title")
        self.now_playing_label.config(text=f"♪ {artist} - {title}")
        
        # Try to play audio if pygame is available
        if self.audio_enabled and PYGAME_AVAILABLE and os.path.exists(track_path):
            try:
                pygame.mixer.music.load(track_path)
                pygame.mixer.music.play()
                self.playing = True
                self.paused = False
                self.play_btn.config(text="⏸")
                self.update_status(f"Playing: {artist} - {title}")
            except Exception as e:
                print(f"Error playing track: {e}")
                self.update_status(f"Error playing: {title}")
        else:
            # Simulation mode
            self.playing = True
            self.paused = False
            self.play_btn.config(text="⏸")
            self.update_status(f"Simulating: {artist} - {title}")
    
    def toggle_playback(self):
        """Toggle play/pause"""
        if not self.current_track:
            # No track selected, try to play first track
            if self.filtered_library:
                self.play_track(self.filtered_library[0])
                self.current_track_index = 0
            return
        
        if self.audio_enabled and PYGAME_AVAILABLE:
            try:
                if self.playing and not self.paused:
                    pygame.mixer.music.pause()
                    self.paused = True
                    self.play_btn.config(text="▶")
                    self.update_status("Paused")
                elif self.paused:
                    pygame.mixer.music.unpause()
                    self.paused = False
                    self.play_btn.config(text="⏸")
                    self.update_status("Resumed")
                else:
                    # Restart the track
                    self.play_track(self.current_track)
            except Exception as e:
                print(f"Error toggling playback: {e}")
        else:
            # Simulation mode
            if self.playing and not self.paused:
                self.paused = True
                self.play_btn.config(text="▶")
                self.update_status("Paused (Simulated)")
            else:
                self.paused = False
                self.play_btn.config(text="⏸")
                self.update_status("Playing (Simulated)")
    
    def stop_playback(self):
        """Stop playback"""
        if self.audio_enabled and PYGAME_AVAILABLE:
            try:
                pygame.mixer.music.stop()
            except:
                pass
        
        self.playing = False
        self.paused = False
        self.play_btn.config(text="▶")
        self.now_playing_label.config(text="♪ Ready")
        self.update_status("Stopped")
    
    def previous_track(self):
        """Play previous track"""
        if not self.filtered_library:
            return
        
        if self.current_track_index > 0:
            self.current_track_index -= 1
        else:
            self.current_track_index = len(self.filtered_library) - 1
        
        track = self.filtered_library[self.current_track_index]
        self.play_track(track)
        
        # Update selection in treeview
        self.tree.selection_set(self.tree.get_children()[self.current_track_index])
    
    def next_track(self):
        """Play next track"""
        if not self.filtered_library:
            return
        
        if self.current_track_index < len(self.filtered_library) - 1:
            self.current_track_index += 1
        else:
            self.current_track_index = 0
        
        track = self.filtered_library[self.current_track_index]
        self.play_track(track)
        
        # Update selection in treeview
        self.tree.selection_set(self.tree.get_children()[self.current_track_index])
    
    def change_volume(self, value):
        """Change volume"""
        self.volume = int(value)
        self.volume_label.config(text=f"{self.volume}%")
        
        if self.audio_enabled and PYGAME_AVAILABLE:
            try:
                pygame.mixer.music.set_volume(self.volume / 100.0)
            except:
                pass
        
        self.save_config()
    
    def change_theme(self, event=None):
        self.current_theme = self.theme_var.get()
        self.apply_theme()
        self.save_config()
        if hasattr(self, 'tree'):
            self.update_track_display()  
    
    def apply_theme(self):
        if self.current_theme not in self.themes:
            self.current_theme = "Matrix Green"
        theme = self.themes[self.current_theme]
        style = ttk.Style()
        self.root.configure(bg=theme["bg_primary"])

        style.configure(
        "Treeview",
        background="#000000",
        foreground=theme["text_primary"],
        fieldbackground="#000000",
        font=("Consolas", 9),
        borderwidth=0,
        highlightthickness=0,
    )

        style.configure(
        "Treeview.Heading",
        background=theme["bg_primary"],
        foreground=theme["text_secondary"],
        font=("Consolas", 9, "bold"),
        borderwidth=1,
        relief="solid",
    )

        style.map(
        "Treeview",
        background=[("selected", theme["selection"])],
        foreground=[("selected", theme["text_primary"])],
    )

        style.map(
        "Treeview.Heading",
        background=[("active", theme["bg_secondary"])],
    )

        style.configure(
        "TCombobox",
        fieldbackground=theme["bg_secondary"],
        background=theme["bg_secondary"],
        foreground=theme["text_primary"],
        borderwidth=1,
        font=("Consolas", 8),
    )

        style.map(
        "TCombobox",
        fieldbackground=[("readonly", theme["bg_secondary"])],
        selectbackground=[("readonly", theme["selection"])],
        selectforeground=[("readonly", theme["text_primary"])],
    )

        style.configure(
        "TNotebook",
        background=theme["bg_primary"],
        borderwidth=0,
    )

        style.configure(
        "TNotebook.Tab",
        background=theme["bg_secondary"],
        foreground=theme["text_secondary"],
        padding=[10, 5],
        font=("Consolas", 9),
    )

        style.map(
        "TNotebook.Tab",
        background=[
            ("selected", theme["bg_primary"]),
            ("active", theme["selection"]),
        ],
        foreground=[
            ("selected", theme["text_primary"]),
            ("active", theme["text_primary"]),
        ],
    )

        if hasattr(self, "tree"):
            try:
            # Force the treeview itself
                self.tree.configure(background="#000000")
            # Force the treeview's parent frame
                self.tree.master.configure(bg="#000000")

            # Nuclear option — force ALL frames to black
                def force_black_recursive(widget):
                    try:
                        cls = widget.winfo_class()
                        if cls == "Frame":
                            widget.configure(bg="#000000")
                        elif cls == "Treeview":
                         widget.configure(background="#000000")
                    except Exception:
                        pass
                    for child in widget.winfo_children():
                        force_black_recursive(child)

                force_black_recursive(self.root)

            except Exception as e:
                print(f"Brute force theming error: {e}")

            
    def _apply_theme_recursive(self, widget, theme):
        widget_class = widget.winfo_class()
        try:
            if widget_class == "Frame":
                current_bg = widget.cget("bg")
                if current_bg in ["#1a1a1a", "#2a2a2a"]:
                    widget.configure(bg=theme["bg_secondary"])
                else:
                    widget.configure(bg=theme["bg_primary"])

            elif widget_class == "Label":
                current_bg = widget.cget("bg")
                text = widget.cget("text")
                if current_bg in ["#1a1a1a", "#2a2a2a"]:
                    widget.configure(bg=theme["bg_secondary"])
                    if "♪" in text and ("TERMMUSIC" in text or "Welcome" in text):
                        widget.configure(fg=theme["accent"])
                    elif any(kw in text.lower() for kw in ["theme:", "search:", "vol:", "library:"]):
                        widget.configure(fg=theme["text_secondary"])
                    else:
                        widget.configure(fg=theme["text_primary"])
                else:
                    widget.configure(bg=theme["bg_primary"])
                    if "♪" in text:
                        widget.configure(fg=theme["accent"])
                    else:
                        widget.configure(fg=theme["text_primary"])

            elif widget_class == "Button":
                widget.configure(
                    bg=theme["bg_secondary"],
                    fg=theme["text_primary"],
                    activebackground=theme["selection"],
                    activeforeground=theme["text_primary"],
                    highlightbackground=theme["border"],
                    highlightcolor=theme["accent"]
                )

            elif widget_class == "Entry":
                widget.configure(
                    bg=theme["bg_secondary"],
                    fg=theme["text_primary"],
                    insertbackground=theme["text_primary"],
                    selectbackground=theme["selection"],
                    selectforeground=theme["text_primary"],
                    highlightbackground=theme["border"],
                    highlightcolor=theme["accent"]
                )

            elif widget_class == "Listbox":
                widget.configure(
                    bg=theme["bg_secondary"],
                    fg=theme["text_primary"],
                    selectbackground=theme["selection"],
                    selectforeground=theme["text_primary"],
                    highlightbackground=theme["border"],
                    highlightcolor=theme["accent"]
                )

            elif widget_class == "LabelFrame":
                widget.configure(
                    bg=theme["bg_primary"],
                    fg=theme["text_secondary"],
                    highlightbackground=theme["border"]
                )

            elif widget_class == "Scale":
                widget.configure(
                    bg=theme["bg_secondary"],
                    fg=theme["text_primary"],
                    troughcolor=theme["bg_primary"],
                    activebackground=theme["accent"],
                    highlightbackground=theme["border"]
                )

            elif widget_class == "Text":
                widget.configure(
                    bg=theme["bg_secondary"],
                    fg=theme["text_primary"],
                    insertbackground=theme["text_primary"],
                    selectbackground=theme["selection"],
                    selectforeground=theme["text_primary"]
                )

            elif widget_class == "Checkbutton":
                widget.configure(
                    bg=theme["bg_primary"],
                    fg=theme["text_primary"],
                    selectcolor=theme["bg_secondary"],
                    activebackground=theme["bg_primary"],
                    activeforeground=theme["text_primary"]
                )

            elif widget_class == "Spinbox":
                widget.configure(
                    bg=theme["bg_secondary"],
                    fg=theme["text_primary"],
                    buttonbackground=theme["bg_secondary"],
                    highlightbackground=theme["border"]
                )

            elif widget_class == "Toplevel":
                widget.configure(bg=theme["bg_primary"])

        except tk.TclError:
            # Some widgets may not support all options; ignore those errors
            pass

        # Recurse into children
        for child in widget.winfo_children():
            self._apply_theme_recursive(child, theme)

            
    def show_settings(self):
        """Show settings dialog"""
        settings_window = tk.Toplevel(self.root)
        settings_window.title("TermMusic Settings")
        settings_window.geometry("500x400")
        settings_window.configure(bg='#0a0a0a')
        settings_window.resizable(False, False)
        
        # Make it modal
        settings_window.transient(self.root)
        settings_window.grab_set()
        
        # Center the window
        settings_window.update_idletasks()
        x = (settings_window.winfo_screenwidth() // 2) - (250)
        y = (settings_window.winfo_screenheight() // 2) - (200)
        settings_window.geometry(f"500x400+{x}+{y}")
        
        # Title
        title_label = tk.Label(settings_window, text="♪ TermMusic Settings", 
                              font=("Consolas", 14, "bold"), bg='#0a0a0a', fg='#ffff00')
        title_label.pack(pady=20)
        
        # Notebook for tabs
        notebook = ttk.Notebook(settings_window)
        notebook.pack(fill=tk.BOTH, expand=True, padx=20, pady=10)
        
        # General tab
        general_frame = tk.Frame(notebook, bg='#0a0a0a')
        notebook.add(general_frame, text="General")
        
        # Dependencies info
        deps_frame = tk.LabelFrame(general_frame, text="Dependencies", 
                                  font=("Consolas", 10, "bold"),
                                  bg='#0a0a0a', fg='#00ff00')
        deps_frame.pack(fill=tk.X, padx=10, pady=10)
        
        deps_info = f"""pygame: {'✓ Available' if PYGAME_AVAILABLE else '✗ Not installed'}
mutagen: {'✓ Available' if MUTAGEN_AVAILABLE else '✗ Not installed'}
spotipy: {'✓ Available' if SPOTIFY_AVAILABLE else '✗ Not installed'}
requests: {'✓ Available' if REQUESTS_AVAILABLE else '✗ Not installed'}"""
        
        deps_label = tk.Label(deps_frame, text=deps_info, 
                             font=("Consolas", 9), bg='#0a0a0a', fg='#00aa00',
                             justify=tk.LEFT)
        deps_label.pack(padx=10, pady=10)
        
        # Keyboard shortcuts
        shortcuts_frame = tk.LabelFrame(general_frame, text="Keyboard Shortcuts", 
                                       font=("Consolas", 10, "bold"),
                                       bg='#0a0a0a', fg='#00ff00')
        shortcuts_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        shortcuts_text = """Space       Play/Pause
Enter       Play selected track
↑/↓         Navigate tracks
←/→         Previous/Next track
F11         Fullscreen
Ctrl+O      Add music folder
Ctrl+,      Settings"""
        
        shortcuts_label = tk.Label(shortcuts_frame, text=shortcuts_text, 
                                  font=("Consolas", 9), bg='#0a0a0a', fg='#00aa00',
                                  justify=tk.LEFT)
        shortcuts_label.pack(padx=10, pady=10)
        
        # Close button
        close_btn = tk.Button(settings_window, text="Close", font=("Consolas", 10),
                             command=settings_window.destroy, bg='#333333', fg='#00ff00')
        close_btn.pack(pady=10)
    
    def setup_keybindings(self):
        """Setup keyboard shortcuts"""
        self.root.bind('<space>', lambda e: self.toggle_playback())
        self.root.bind('<Return>', lambda e: self.play_selected_track())
        self.root.bind('<Up>', lambda e: self.navigate_track(-1))
        self.root.bind('<Down>', lambda e: self.navigate_track(1))
        self.root.bind('<Left>', lambda e: self.previous_track())
        self.root.bind('<Right>', lambda e: self.next_track())
        self.root.bind('<F11>', lambda e: self.toggle_fullscreen())
        self.root.bind('<Control-o>', lambda e: self.add_music_folder())
        self.root.bind('<Control-comma>', lambda e: self.show_settings())
        self.root.focus_set()
        
    def add_music_folder(self):
        folder = filedialog.askdirectory(
        title="Select Music Folder",
        parent=self.root
        )
        if not folder:
                return
        if folder not in self.library_paths:
                self.library_paths.append(folder)
                self.active_library_path = folder
                self.save_config()
                self.scan_folder(folder)
                self.update_playlist_info()
                messagebox.showinfo(
                "Folder Added",
                f"Added music folder:\n{folder}",
                parent=self.root
            )
        else:
            messagebox.showinfo(
                "Folder Already Added",
                f"That folder is already in your library:\n{folder}",
                parent=self.root
            )

    def navigate_track(self, direction):
        """Navigate track selection"""
        selection = self.tree.selection()
        if not selection:
            if self.tree.get_children():
                self.tree.selection_set(self.tree.get_children()[0])
            return
        
        current_item = selection[0]
        current_index = self.tree.index(current_item)
        children = self.tree.get_children()
        
        if direction == -1 and current_index > 0:
            new_item = children[current_index - 1]
        elif direction == 1 and current_index < len(children) - 1:
            new_item = children[current_index + 1]
        else:
            return
        
        self.tree.selection_set(new_item)
        self.tree.see(new_item)
    
    def toggle_fullscreen(self):
        """Toggle fullscreen mode"""
        current_state = self.root.attributes('-fullscreen')
        self.root.attributes('-fullscreen', not current_state)
    
    def update_status(self, message):
        """Update status bar message"""
        base_status = f"Audio: {'Enabled' if self.audio_enabled else 'Disabled'} | F11: Fullscreen | Space: Play/Pause"
        self.status_label.config(text=f"{message} | {base_status}")
    
    def update_loop(self):
        """Main update loop for real-time status"""
        while True:
            try:
                if self.audio_enabled and PYGAME_AVAILABLE and self.playing:
                    # Check if music is still playing
                    if not pygame.mixer.music.get_busy() and not self.paused:
                        # Song ended, play next
                        self.next_track()
                
                time.sleep(0.1)
            except:
                break
    
    def on_closing(self):
        """Handle application closing"""
        self.save_config()
        if self.audio_enabled and PYGAME_AVAILABLE:
            try:
                pygame.mixer.quit()
            except:
                pass
        self.root.destroy()

def main():
    try:
        app = TerminalMusicPlayer()
        app.root.mainloop()
    except KeyboardInterrupt:
        print("\nTermMusic terminated by user")
    except Exception as e:
        print(f"Error starting TermMusic: {e}")

if __name__ == "__main__":
    main()