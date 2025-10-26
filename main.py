import os
import math
import threading
import tkinter as tk
from tkinter import filedialog, messagebox
import ttkbootstrap as tb
from PIL import Image, ImageTk
import numpy as np

# try import opencv
try:
    import cv2
    CV2_AVAILABLE = True
except Exception:
    CV2_AVAILABLE = False

# try import tkinterdnd2 for Drag&Drop (optional)
try:
    from tkinterdnd2 import DND_FILES, TkinterDnD
    DND_AVAILABLE = True
except Exception:
    DND_AVAILABLE = False
    DND_FILES = None
    TkinterDnD = None
    print("Hinweis: 'tkinterdnd2' nicht gefunden. Drag & Drop ist deaktiviert. Installieren mit: pip install tkinterdnd2")

# -------------------------
# Utilities
# -------------------------
def unique_path(path):
    base, ext = os.path.splitext(path)
    i = 1
    out = path
    while os.path.exists(out):
        out = f"{base}_{i}{ext}"
        i += 1
    return out

def polygon_area(poly):
    if not poly or len(poly) < 3:
        return 0.0
    area = 0.0
    for i in range(len(poly)):
        x1,y1 = poly[i]
        x2,y2 = poly[(i+1) % len(poly)]
        area += x1*y2 - x2*y1
    return abs(area) * 0.5

# Sutherland–Hodgman half-plane clip
def clip_polygon_halfplane(polygon, a, b, c):
    if not polygon:
        return []
    def inside(pt):
        return a * pt[0] + b * pt[1] + c >= -1e-9
    def intersect(p1, p2):
        x1, y1 = p1; x2, y2 = p2
        v1 = a*x1 + b*y1 + c
        v2 = a*x2 + b*y2 + c
        denom = (v1 - v2)
        if abs(denom) < 1e-12:
            return p2
        t = v1 / (v1 - v2)
        xi = x1 + t * (x2 - x1)
        yi = y1 + t * (y2 - y1)
        return (xi, yi)
    input_list = polygon[:]
    if not input_list:
        return []
    output_list = []
    S = input_list[-1]
    for E in input_list:
        if inside(E):
            if inside(S):
                output_list.append(E)
            else:
                output_list.append(intersect(S, E))
                output_list.append(E)
        else:
            if inside(S):
                output_list.append(intersect(S, E))
        S = E
    return output_list

# -------------------------
# Separator: vertical default, both endpoints movable, fixed length
# Added: single rotation handle near middle (right side), ctrl-5° snapping, angle display box and +90° button
# -------------------------
class Separator:
    HANDLE_R = 7
    ROT_HANDLE_R = 12  # radius for rotation handle visual/hit area
    ROT_OFFSET = 26    # distance from center to place rot handle along perpendicular
    ANGLE_BOX_W = 64
    ANGLE_BOX_H = 28
    BUTTON_W = 48
    BUTTON_H = 20
    BUTTON_MARGIN = 6

    def __init__(self, cx, cy, angle=0.0, length=1000):
        """
        cx, cy: center (display coords)
        angle: rotation in radians from vertical (0 = vertical)
        length: total length in display coords (should be set to max(image dim))
        """
        self.cx = float(cx)
        self.cy = float(cy)
        self.angle = float(angle)   # radians
        self.length = float(length)
        self.selected = False

        # canvas ids (set by draw_on_canvas)
        self.line_id = None
        self.handle_top_id = None
        self.handle_bot_id = None

        # single rotation handle (we only draw right-side handle)
        self.rot_id = None
        self.rot_text_tag = f"rot_text_{id(self)}"

        # +90° button drawn under rot handle
        self.btn_id_bg = None
        self.btn_id_text = None
        self.btn_tag = f"rot_button_{id(self)}"

        # reset-button
        self.reset_id_bg = None
        self.reset_id_text = None
        self.reset_tag = f"reset_button_{id(self)}"


        # angle display box tag
        self.angle_box_tag = f"angle_box_{id(self)}"
        self.angle_text_tag = f"angle_text_{id(self)}"

    def endpoints(self):
        """Return (x1,y1,x2,y2) in display coords. Top is first (per vertical orientation)."""
        half = self.length / 2.0
        # axis vector for the separator (angle=0 -> vertical)
        sa = math.sin(self.angle)
        ca = math.cos(self.angle)
        dx = sa * half
        dy = ca * half
        x_top = self.cx + dx
        y_top = self.cy - dy
        x_bot = self.cx - dx
        y_bot = self.cy + dy
        return (x_top, y_top, x_bot, y_bot)

    def top_handle(self):
        x1, y1, x2, y2 = self.endpoints()
        return (x1, y1)

    def bot_handle(self):
        x1, y1, x2, y2 = self.endpoints()
        return (x2, y2)

    def distance_to_line(self, px, py):
        x1, y1, x2, y2 = self.endpoints()
        vx = x2 - x1; vy = y2 - y1
        wx = px - x1; wy = py - y1
        denom = math.hypot(vx, vy)
        if denom == 0:
            return math.hypot(px - x1, py - y1)
        return abs(vx*wy - vy*wx) / denom

    def set_top_handle(self, px, py):
        """Move top handle to (px,py) — adjust angle, keep center and length fixed."""
        vx = px - self.cx
        vy = self.cy - py  # note reversed to get consistent angle definition
        half = self.length / 2.0
        if abs(vx) < 1e-6 and abs(vy) < 1e-6:
            return
        self.angle = math.atan2(vx, vy)

    def set_bot_handle(self, px, py):
        """Move bottom handle to (px,py) — adjust angle, keep center and length fixed."""
        vx = px - self.cx
        vy = py - self.cy
        half = self.length / 2.0
        if abs(vx) < 1e-6 and abs(vy) < 1e-6:
            return
        self.angle = math.atan2(-vx, vy)

    def move_by(self, dx, dy):
        """Translate separator by dx, dy in display coords."""
        self.cx += dx
        self.cy += dy

    def clamp_to_bounds(self, minx, miny, maxx, maxy):
        """Ensure center remains within bounds so endpoints stay visible (best effort)."""
        self.cx = max(minx + 1, min(self.cx, maxx - 1))
        self.cy = max(miny + 1, min(self.cy, maxy - 1))

    def reset_angle(self):
        """Setzt den Winkel auf 0° (vertikal)."""
        self.angle = 0.0

    # -------------------------
    # Rotation handle helpers (single right-side handle)
    # -------------------------
    def rot_handle_position(self):
        """
        Compute a single position (right) near the center to display rotation control.
        Places it along the *perpendicular* to the separator axis so it sits beside the line.
        """
        # perpendicular to axis vector is (cos(angle), sin(angle))
        px = math.cos(self.angle)
        py = math.sin(self.angle)
        ox = px * self.ROT_OFFSET
        oy = py * self.ROT_OFFSET
        # single handle on the "right" side (positive along perpendicular)
        right = (self.cx + ox, self.cy + oy)
        return right

    def draw_on_canvas(self, canvas):
        """Create or update the canvas items for this separator."""
        # remove any existing items (we redraw fully)
        # Delete items safely
        global ry, rx
        for attr in ("line_id","handle_top_id","handle_bot_id","rot_id","btn_id_bg","btn_id_text"):
            if getattr(self, attr, None):
                try:
                    canvas.delete(getattr(self, attr))
                except Exception:
                    pass
                setattr(self, attr, None)
        # also remove text tags if present
        try:
            canvas.delete(self.rot_text_tag)
        except Exception:
            pass
        try:
            canvas.delete(self.btn_tag)
        except Exception:
            pass
        try:
            canvas.delete(self.angle_box_tag)
            canvas.delete(self.angle_text_tag)
        except Exception:
            pass

        # main line
        x1,y1,x2,y2 = self.endpoints()
        color = "#00ff66" if self.selected else "#66ff99"
        self.line_id = canvas.create_line(x1,y1,x2,y2, width=3, fill=color)

        # top/bot handles (small circles)
        hx1, hy1 = x1, y1
        hx2, hy2 = x2, y2
        self.handle_top_id = canvas.create_oval(hx1 - self.HANDLE_R, hy1 - self.HANDLE_R,
                                                hx1 + self.HANDLE_R, hy1 + self.HANDLE_R,
                                                fill="#ffcc00" if self.selected else "#ffaa00", outline="black")
        self.handle_bot_id = canvas.create_oval(hx2 - self.HANDLE_R, hy2 - self.HANDLE_R,
                                                hx2 + self.HANDLE_R, hy2 + self.HANDLE_R,
                                                fill="#ffcc00" if self.selected else "#ffaa00", outline="black")

        # rotation handle (single) and its arrow text
        if True:
            rx, ry = self.rot_handle_position()
            self.rot_id = canvas.create_oval(rx - self.ROT_HANDLE_R, ry - self.ROT_HANDLE_R,
                                             rx + self.ROT_HANDLE_R, ry + self.ROT_HANDLE_R,
                                             fill="#ffffff", outline="#666666")
            # draw a half-circle-like arrow text (we use ↻)
            canvas.create_text(rx, ry, text="↻", fill="#333333", font=("Arial", 12), tags=(self.rot_text_tag,))

        # +90° Button (below the single rot handle)
        bx = rx
        by = ry + self.ROT_HANDLE_R + self.BUTTON_MARGIN
        half_w = self.BUTTON_W / 2.0
        self.btn_id_bg = canvas.create_rectangle(bx - half_w, by, bx + half_w, by + self.BUTTON_H,
                                                fill="#ffffff", outline="#000000", tags=(self.btn_tag,))
        self.btn_id_text = canvas.create_text(bx, by + self.BUTTON_H/2.0, text="+90°", fill="#000000",
                                              font=("Arial", 10, "bold"), tags=(self.btn_tag,))

        # Reset Button (below +90°)
        by_reset = by + self.BUTTON_H + self.BUTTON_MARGIN
        self.reset_id_bg = canvas.create_rectangle(
            bx - half_w, by_reset, bx + half_w, by_reset + self.BUTTON_H,
            fill="#ffffff", outline="#000000", tags=(self.reset_tag,))
        self.reset_id_text = canvas.create_text(
            bx, by_reset + self.BUTTON_H/2.0, text="Reset", fill="#000000",
            font=("Arial", 10, "bold"), tags=(self.reset_tag,))

        # Angle box (only show when selected) — we keep it drawn here but visible only when selected
        if self.selected:
            self._draw_angle_box(canvas)
        # done

    def _draw_angle_box(self, canvas):
        """Draw white rectangle with black text showing angle (degrees)."""
        try:
            canvas.delete(self.angle_box_tag)
        except Exception:
            pass
        try:
            canvas.delete(self.angle_text_tag)
        except Exception:
            pass
        # compute position to the right of the rot handle (or fallback to right of center)
        rx, ry = self.rot_handle_position()
        box_x = rx + 18
        box_y = ry - 16
        x1 = box_x
        y1 = box_y
        x2 = x1 + self.ANGLE_BOX_W
        y2 = y1 + self.ANGLE_BOX_H
        # rectangle + text (black on white)
        canvas.create_rectangle(x1, y1, x2, y2, fill="#ffffff", outline="#000000", tags=(self.angle_box_tag,))
        angle_deg = (math.degrees(self.angle)) % 360.0
        txt = f"{angle_deg:6.1f}°"
        canvas.create_text((x1 + x2)/2.0, (y1 + y2)/2.0, text=txt, fill="#000000",
                           font=("Consolas", 11, "bold"), tags=(self.angle_text_tag,))

    def delete_rot_texts(self, canvas):
        try:
            canvas.delete(self.rot_text_tag)
        except Exception:
            pass
        try:
            canvas.delete(self.btn_tag)
        except Exception:
            pass
        try:
            canvas.delete(self.angle_box_tag)
            canvas.delete(self.angle_text_tag)
        except Exception:
            pass
        try:
            canvas.delete(self.reset_tag)
        except Exception:
            pass

    def hit_test_rot_handle(self, px, py):
        """
        Returns:
          'rot' if point (px,py) is over the rotation handle center area,
          'button' if on +90° button,
          'reset' if on Reset button,
          otherwise None.
        """
        rx, ry = self.rot_handle_position()
        # handle hit
        if (px - rx) ** 2 + (py - ry) ** 2 <= (self.ROT_HANDLE_R + 6) ** 2:
            return 'rot'
        # +90° button hit
        bx = rx
        by = ry + self.ROT_HANDLE_R + self.BUTTON_MARGIN
        half_w = self.BUTTON_W / 2.0
        if (bx - half_w) <= px <= (bx + half_w) and by <= py <= (by + self.BUTTON_H):
            return 'button'
        # reset button hit (below +90°)
        by_reset = by + self.BUTTON_H + self.BUTTON_MARGIN
        if (bx - half_w) <= px <= (bx + half_w) and by_reset <= py <= (by_reset + self.BUTTON_H):
            return 'reset'
        return None


# -------------------------
# Auto-crop helpers (feature matching + affine)
# -------------------------
def create_feature_detector():
    """Try to create SIFT; fallback to ORB if not available."""
    if not CV2_AVAILABLE:
        return None, None
    try:
        sift = cv2.SIFT_create()
        matcher = cv2.BFMatcher(cv2.NORM_L2, crossCheck=False)
        return sift, matcher
    except Exception:
        try:
            orb = cv2.ORB_create(1500)
            matcher = cv2.BFMatcher(cv2.NORM_HAMMING, crossCheck=False)
            return orb, matcher
        except Exception:
            return None, None

def estimate_affine_from_features(detector, matcher, img1_gray, img2_gray, max_matches=200):
    """
    Detect features and estimate affine transform from img1->img2.
    Returns (dx, dy, angle_deg) or (0,0,0) on failure.
    """
    if detector is None or matcher is None:
        return (0.0, 0.0, 0.0)
    try:
        k1, d1 = detector.detectAndCompute(img1_gray, None)
        k2, d2 = detector.detectAndCompute(img2_gray, None)
        if d1 is None or d2 is None or len(k1) < 4 or len(k2) < 4:
            return (0.0, 0.0, 0.0)
        if hasattr(matcher, 'knnMatch'):
            matches = matcher.knnMatch(d1, d2, k=2)
            good = []
            for m_n in matches:
                if len(m_n) < 2:
                    continue
                m, n = m_n
                if m.distance < 0.75 * n.distance:
                    good.append(m)
            matches = sorted(good, key=lambda x: x.distance)[:max_matches]
        else:
            matches = matcher.match(d1, d2)
            matches = sorted(matches, key=lambda x: x.distance)[:max_matches]
        if len(matches) < 4:
            return (0.0, 0.0, 0.0)
        pts1 = np.float32([k1[m.queryIdx].pt for m in matches]).reshape(-1,1,2)
        pts2 = np.float32([k2[m.trainIdx].pt for m in matches]).reshape(-1,1,2)
        M, inliers = cv2.estimateAffinePartial2D(pts1, pts2, method=cv2.RANSAC, ransacReprojThreshold=5.0)
        if M is None:
            return (0.0, 0.0, 0.0)
        dx = M[0,2]; dy = M[1,2]
        angle_rad = math.atan2(M[1,0], M[0,0])
        angle_deg = math.degrees(angle_rad)
        return (float(dx), float(dy), float(angle_deg))
    except Exception as e:
        return (0.0, 0.0, 0.0)

# -------------------------
# Main Application class
# -------------------------
class ImageCropSplitterApp:
    def __init__(self, root):
        self.root = root
        self.root.title("Crop + Vertical Rotatable Separators")
        self.style = tb.Style(theme="cyborg")
        self.win = root

        # UI state ...
        self.reference_crop = None
        self.last_crop = None

        # Data
        self.image_paths = []
        self.current_index = 0
        ### NEU: Zustände pro Bild (für Crop + Trennen)
        self.image_states = {}  # {path: {"crop": True, "trennen": False}}
        self.base_image = None      # PIL original
        self.display_image = None   # PIL resized for canvas
        self.tk_image = None
        self.zoom = 1.0

        # crop
        self.crop_disp = None   # tuple display coords (x1,y1,x2,y2)
        self.crop_orig = None   # tuple original image coords (ox1,oy1,ox2,oy2)

        # Auto-Crop Referenz
        self.reference_crop = None          # (x1,y1,x2,y2) – dein erster, manueller Crop
        self.last_crop = None               # letzter gültiger Crop
        self.ref_template_gray = None       # gespeicherte Template-Vorlage (Graustufen) aus reference_crop
        self.last_scale = 1.0               # sanft geglättete Skalierung
        self.last_rotation = 0.0            # sanft geglättete Rotation

        # separators
        self.separators = []    # list[Separator]
        self.selected_sep = None
        self.sep_mode = None    # 'move_top','move_bot','move_line','rotate', None
        self.sep_drag_offset = None
        self.rotation_handle_active = None  # 'rot' when rotating

        # interaction
        self.dragging = False
        self.resizing = False
        self.resize_edge = None
        self.rect_before = None
        self.drag_start = None

        # UI state
        self.auto_crop_var = tk.BooleanVar(value=False)
        self.progress_var = tk.DoubleVar(value=0.0)

        # format vars in menu
        self.format_vars = {
            "jpeg": tk.BooleanVar(value=True),
            "png": tk.BooleanVar(value=False),
            "tiff": tk.BooleanVar(value=False),
            "bmp": tk.BooleanVar(value=False),
            "pdf": tk.BooleanVar(value=False),
        }

        # feature detector objects for auto-crop
        self.detector, self.matcher = create_feature_detector()

        # build GUI
        self.build_gui()

        self.crop_disp = None
        self.crop_orig = None
        self.separators = []
        self.selected_sep = None

        # binds
        self.win.bind("<Escape>", self.on_escape)
        self.win.bind("<Delete>", self.on_delete_key)
        self.win.bind("<Configure>", self.on_configure)

    def build_gui(self):
        main = tb.Frame(self.win)
        main.pack(fill="both", expand=True)

        # left file list
        left = tb.Frame(main, width=260, bootstyle="dark")
        left.pack(side="left", fill="y", padx=6, pady=6)
        ### ERSETZT: Neue Treeview-Tabelle mit Checkbox-Spalten
        from tkinter import ttk
        tb.Label(left, text="Geladene Bilder", bootstyle="inverse-dark").pack(anchor="w", padx=6, pady=(6, 2))

        columns = ("Bild", "Crop", "Trennen")
        self.tree = ttk.Treeview(left, columns=columns, show="headings", height=15)

        self.tree.heading("Bild", text="Bild")
        self.tree.heading("Crop", text="Crop")
        self.tree.heading("Trennen", text="Trennen")

        self.tree.column("Bild", width=120, anchor="w")
        self.tree.column("Crop", width=40, anchor="center")
        self.tree.column("Trennen", width=60, anchor="center")

        self.tree.pack(fill="both", expand=True, padx=6, pady=6)
        self.tree.bind("<Button-1>", self.on_tree_click)
        self.tree.bind("<<TreeviewSelect>>", self.on_tree_select)

        tb.Button(left, text="Alle Löschen", command=self.delete_all_images, bootstyle="danger").pack(fill="x", padx=6,
                                                                                                      pady=4)

        # If DnD available: register treeview for drops
        if DND_AVAILABLE:
            try:
                self.tree.drop_target_register(DND_FILES)
                self.tree.dnd_bind('<<Drop>>', self.on_drop_files)
            except Exception as e:
                print("Warning: failed to register DnD on treeview:", e)

        # right area with toolbar & canvas
        right = tb.Frame(main)
        right.pack(side="right", fill="both", expand=True, padx=6, pady=6)

        # toolbar (store as attribute so we can add menu)
        self.toolbar = tb.Frame(right)
        self.toolbar.pack(fill="x", pady=(4,2))

        tb.Button(self.toolbar, text="Bilder laden", command=self.load_files, bootstyle="primary").pack(side="left", padx=4)
        tb.Button(self.toolbar, text="Zielordner", command=self.select_output_folder, bootstyle="primary").pack(side="left", padx=4)
        tb.Button(self.toolbar, text="Vorheriges Bild", command=self.prev_image, bootstyle="info").pack(side="left", padx=4)
        tb.Button(self.toolbar, text="Nächstes Bild", command=self.next_image, bootstyle="info").pack(side="left", padx=4)

        # --- Neue Toggle-Schalter für Crop und Trennbalken ---
        self.show_crop_var = tk.BooleanVar(value=False)
        self.show_separator_var = tk.BooleanVar(value=False)

        tb.Checkbutton(
            self.toolbar,
            text="Crop-Bereich",
            variable=self.show_crop_var,
            bootstyle="info-round-toggle",
            command=self.toggle_crop_area
        ).pack(side="left", padx=6)

        tb.Checkbutton(
            self.toolbar,
            text="Trennbalken",
            variable=self.show_separator_var,
            bootstyle="warning-round-toggle",
            command=self.toggle_separator
        ).pack(side="left", padx=6)

        # Format dropdown (Menubutton with checkbuttons) - visible in toolbar
        self.format_menubutton = tk.Menubutton(self.toolbar, text="Formate", relief="raised")
        self.format_menu = tk.Menu(self.format_menubutton, tearoff=False)
        for k in ("jpeg","png","tiff","bmp","pdf"):
            self.format_menu.add_checkbutton(label=k.upper(), variable=self.format_vars[k])
        self.format_menubutton.config(menu=self.format_menu)
        self.format_menubutton.pack(side="left", padx=6)

        # spacer
        spacer = tb.Label(self.toolbar, text="")
        spacer.pack(side="left", expand=True)

        self.auto_crop_check = tb.Checkbutton(
            self.toolbar,
            text="Smart-Crop (experimental)",
            variable=self.auto_crop_var,
            bootstyle="success-round-toggle"
        )
        self.auto_crop_check.pack(side="right", padx=6)
        self.auto_crop_check.configure(state="normal")
        self.update_auto_crop_state()

        tb.Button(self.toolbar, text="Alle bearbeiten", command=self.crop_all_threaded, bootstyle="success").pack(side="right", padx=4)
        tb.Button(self.toolbar, text="Einmal bearbeiten", command=self.crop_single, bootstyle="success").pack(side="right", padx=4)

        self.stop_flag = threading.Event()  # Wird genutzt, um Threads sauber zu stoppen

        tb.Button(
            self.toolbar,
            text="❌ Stopp",
            command=self.stop_all_processes,
            bootstyle="danger"
        ).pack(side="right", padx=4)

        # canvas
        self.canvas = tk.Canvas(right, bg="#222", cursor="cross", highlightthickness=0)
        self.canvas.pack(fill="both", expand=True, pady=(4,4))
        self.canvas.bind("<ButtonPress-1>", self.canvas_down)
        self.canvas.bind("<B1-Motion>", self.canvas_move)
        self.canvas.bind("<ButtonRelease-1>", self.canvas_up)
        self.canvas.bind("<Motion>", self.canvas_motion)
        self.canvas.bind("<MouseWheel>", self.on_mousewheel)
        self.canvas.bind("<Button-4>", self.on_mousewheel_linux)
        self.canvas.bind("<Button-5>", self.on_mousewheel_linux)

        # If DnD available: register canvas and whole window for drops (so dragging to any empty area works)
        if DND_AVAILABLE:
            try:
                self.canvas.drop_target_register(DND_FILES)
                self.canvas.dnd_bind('<<Drop>>', self.on_drop_files)
            except Exception as e:
                print("Warning: failed to register DnD on canvas:", e)
            try:
                # Some platforms support registering the root window itself
                if hasattr(self.win, "drop_target_register"):
                    self.win.drop_target_register(DND_FILES)
                    self.win.dnd_bind('<<Drop>>', self.on_drop_files)
            except Exception as e:
                print("Warning: failed to register DnD on window:", e)

        # progress at bottom
        bottombar = tb.Frame(self.win)
        bottombar.pack(side="bottom", fill="x")
        self.progress = tb.Progressbar(bottombar, bootstyle="success", variable=self.progress_var, maximum=100)
        self.progress.pack(fill="x", padx=6, pady=6)

    def update_auto_crop_state(self):
        """Aktiviert den 'Auto-Crop pro Bild'-Schalter nur, wenn Voraussetzungen erfüllt sind."""
        enable = (self.base_image is not None) and (self.crop_orig is not None) and CV2_AVAILABLE
        try:
            self.auto_crop_check.configure(state=("normal" if enable else "disabled"))
        except Exception:
            pass

    def _clamp_rect_to_image(self, x1, y1, x2, y2, img_w, img_h):
        x1 = max(0, min(x1, img_w - 5))
        y1 = max(0, min(y1, img_h - 5))
        x2 = max(x1 + 5, min(x2, img_w))
        y2 = max(y1 + 5, min(y2, img_h))
        return int(x1), int(y1), int(x2), int(y2)


    def stop_all_processes(self):
        """Stoppt laufende Crop-Prozesse und setzt Fortschritt zurück."""
        print("[STOP] Stop-Anforderung erhalten.")
        self.stop_flag.set()  # Signal an Threads
        self.progress_var.set(0)
        self.progress.update_idletasks()
        messagebox.showinfo("Abgebrochen", "Alle Prozesse wurden gestoppt.")

    # -------------------------
    # Drag & Drop handler
    # -------------------------
    def on_drop_files(self, event):
        """
        Handler für Drag&Drop von Dateien in die Listbox oder das Fenster.
        - Dateien werden am Ende der Liste hinzugefügt.
        - Danach wird automatisch das erste Bild in der Liste angezeigt.
        """
        try:
            files = self.root.splitlist(event.data)
            # Unterstützte Formate
            supported_exts = ('.png', '.jpg', '.jpeg', '.bmp', '.tiff', '.tif')
            new_files = [f for f in files if f.lower().endswith(supported_exts)]

            if not new_files:
                messagebox.showwarning("Keine Bilder", "Keine unterstützten Bilddateien gefunden.")
                return

            # Füge neue Dateien hinzu (am Ende)
            added = [f for f in new_files if f not in self.image_paths]
            if added:
                self.image_paths.extend(added)
                self.image_paths.sort()
                for f in added:
                    self.image_states[f] = {"crop": True, "trennen": False}
                self.update_tree()
                self.update_tree()

                # Zeige IMMER das erste Bild in der Liste nach Drag&Drop
                if self.image_paths:
                    self.current_index = 0
                    self.load_current_image()

        except Exception as e:
            messagebox.showerror("Fehler beim Drag&Drop", str(e))

    # -------------------------
    # File handling & navigation
    # -------------------------
    def load_files(self):
        files = filedialog.askopenfilenames(title="Bilder auswählen",
                                            filetypes=[("Bilder","*.png;*.jpg;*.jpeg;*.bmp;*.tiff;*.tif")])
        if not files:
            return
        new = [f for f in files if f not in self.image_paths]
        if new:
            # original behaviour sorted; keep it for load_files
            self.image_paths.extend(new)
        self.image_paths.sort()
        for f in new:
            self.image_states[f] = {"crop": True, "trennen": False}
        self.update_tree()
        self.update_tree()
        if self.base_image is None:
            self.current_index = 0
            self.load_current_image()

    def select_output_folder(self):
        folder = filedialog.askdirectory(title="Zielordner auswählen")
        if folder:
            self.output_folder = folder

    ### NEU
    def update_tree(self):
        # Clear Tree
        for i in self.tree.get_children():
            self.tree.delete(i)

        for path in self.image_paths:
            name = os.path.basename(path)
            state = self.image_states.get(path, {"crop": True, "trennen": False})
            crop_symbol = "✓" if state["crop"] else ""
            trenn_symbol = "✓" if state["trennen"] else ""
            self.tree.insert("", "end", values=(name, crop_symbol, trenn_symbol))

    def on_tree_select(self, event):
        """Zeigt das ausgewählte Bild aus der Treeview-Liste im Vorschaufenster."""
        selected_item = self.tree.focus()
        if not selected_item:
            return

        values = self.tree.item(selected_item, "values")
        if not values or len(values) == 0:
            return

        name = values[0]
        path = next((p for p in self.image_paths if os.path.basename(p) == name), None)
        if not path:
            return

        # Lade das entsprechende Bild
        try:
            self.current_index = self.image_paths.index(path)
            self.load_current_image()
        except Exception as e:
            print("❌ Fehler beim Laden des ausgewählten Bildes:", e)

    def delete_all_images(self):
        self.image_paths.clear()
        self.image_states.clear()
        self.update_tree()
        self.update_tree()
        self.base_image = None
        self.display_image = None
        self.crop_disp = None
        self.crop_orig = None
        self.separators.clear()
        self.selected_sep = None
        self.canvas.delete("all")
        self.update_auto_crop_state()

    def on_tree_click(self, event):
        """Toggle Crop/Trennen Checkboxen durch Klick auf die Spalte."""
        region = self.tree.identify("region", event.x, event.y)
        if region != "cell":
            return

        col = self.tree.identify_column(event.x)
        row_id = self.tree.identify_row(event.y)
        if not row_id:
            return

        values = self.tree.item(row_id, "values")
        if not values:
            return

        name = values[0]
        path = next((p for p in self.image_paths if os.path.basename(p) == name), None)
        if not path:
            return

        state = self.image_states.get(path, {"crop": True, "trennen": False})

        if col == "#2":  # Crop
            state["crop"] = not state["crop"]
        elif col == "#3":  # Trennen
            state["trennen"] = not state["trennen"]

        self.image_states[path] = state
        self.update_tree()

    def prev_image(self):
        if not self.image_paths:
            return
        self.current_index = (self.current_index - 1) % len(self.image_paths)
        self.update_tree()
        self.load_current_image()

    def next_image(self):
        if not self.image_paths:
            return
        self.current_index = (self.current_index + 1) % len(self.image_paths)
        self.update_tree()
        self.load_current_image()

    # -------------------------
    # Image loading & display
    # -------------------------
    def load_current_image(self):
        if not self.image_paths:
            self.canvas.delete("all")
            self.base_image = None; return
        path = self.image_paths[self.current_index]
        try:
            img = Image.open(path).convert("RGB")
        except Exception as e:
            messagebox.showerror("Fehler", f"Kann Bild nicht laden:\n{e}")
            return
        self.base_image = img
        self.zoom = 1.0
        self.display_image = self.get_display_image()
        # set default crop_disp only if user enabled the Crop toggle
        # (so loading images does NOT automatically show a crop)
        if not self.crop_disp and getattr(self, "show_crop_var", None) and self.show_crop_var.get():
            dw, dh = self.display_image.size
            # default crop: full image with small margin
            margin = 0.02
            self.crop_disp = (dw * margin, dh * margin, dw * (1 - margin), dh * (1 - margin))
            self._update_crop_orig_from_disp()

        # Wenn der Benutzer den Crop verändert hat, neue Referenz setzen
        if self.crop_orig:
            self.reference_crop = tuple(map(int, self.crop_orig))
            self.last_crop = self.reference_crop
            self.ref_template_gray = None  # erzwingt Neuaufbau der Vorlage auf dem nächsten Bild
            self.last_scale = 1.0
            self.last_rotation = 0.0

        # ensure separators length updated to image size
        self._update_separators_length()
        self.redraw()
        self.win.title(f"Crop Splitter - {os.path.basename(path)}")
        self.update_auto_crop_state()

    def get_display_image(self):
        if self.base_image is None:
            return None
        cw = max(10, self.canvas.winfo_width())
        ch = max(10, self.canvas.winfo_height())
        iw, ih = self.base_image.size
        scale = min(cw/iw, ch/ih)
        scale *= self.zoom
        new_size = (max(1, int(iw*scale)), max(1, int(ih*scale)))
        return self.base_image.resize(new_size, Image.LANCZOS)

    # -------------------------
    # Canvas drawing & redraw
    # -------------------------
    def redraw(self):
        # clear canvas and redraw everything including separators (with rot handle / button / angle box)
        self.canvas.delete("all")
        if self.display_image:
            self.tk_image = ImageTk.PhotoImage(self.display_image)
            self.canvas.create_image(0,0,anchor="nw", image=self.tk_image)
        # crop rect + Griffe (Ecken & Kanten)
        if self.crop_disp:
            x1, y1, x2, y2 = self.crop_disp
            self.canvas.create_rectangle(x1, y1, x2, y2, outline="red", width=2)

            # Griffgröße
            r = 6

            # Ecken
            corners = [
                (x1, y1), (x2, y1),
                (x2, y2), (x1, y2)
            ]
            # Mittelpunkte der Kanten
            mids = [
                ((x1 + x2) / 2, y1),  # oben
                (x2, (y1 + y2) / 2),  # rechts
                ((x1 + x2) / 2, y2),  # unten
                (x1, (y1 + y2) / 2)  # links
            ]

            # Ecken zeichnen (rot)
            for (cx, cy) in corners:
                self.canvas.create_rectangle(cx - r, cy - r, cx + r, cy + r,
                                             fill="#ff3333", outline="black")

            # Kanten-Mittelpunkte zeichnen (orange)
            for (cx, cy) in mids:
                self.canvas.create_rectangle(cx - r, cy - r, cx + r, cy + r,
                                             fill="#ffaa00", outline="black")

        # separators
        for sep in self.separators:
            sep.draw_on_canvas(self.canvas)

    # -------------------------
    # Canvas interaction
    # -------------------------
    def canvas_down(self, event):
        x, y = event.x, event.y
        # Nur aktivieren, wenn der Benutzer KEINEN Separator anklickt
        clicked_on_separator = False

        # Prüfe, ob Klick auf Linie oder Griffe eines Trennbalkens erfolgt ist
        for sep in self.separators:
            if sep.distance_to_line(event.x, event.y) < 8:
                clicked_on_separator = True
                break
            hx1, hy1 = sep.top_handle()
            hx2, hy2 = sep.bot_handle()
            if ((event.x - hx1) ** 2 + (event.y - hy1) ** 2 <= (sep.HANDLE_R + 6) ** 2 or
                    (event.x - hx2) ** 2 + (event.y - hy2) ** 2 <= (sep.HANDLE_R + 6) ** 2):
                clicked_on_separator = True
                break

        # Nur aktivieren, wenn der Benutzer NICHT auf einen Separator klickt
        if not clicked_on_separator and hasattr(self, "show_crop_var") and not self.show_crop_var.get():
            self.show_crop_var.set(True)
            print("[Auto] Crop-Bereich aktiviert durch Benutzeraktion (Zeichnen)")

        # check rotation handle / button first (for rotation or +90°)
        for sep in reversed(self.separators):
            # compute hit test against rotation handle and button
            hit = sep.hit_test_rot_handle(x, y)
            if hit is not None:
                self._select_separator(sep)
                if hit == 'button':
                    # rotate +90° immediately
                    sep.angle += math.radians(90.0)
                    # normalize
                    sep.angle = (sep.angle + math.pi*2) % (math.pi*2)
                    # redraw with angle box visible
                    sep.selected = True
                    sep.draw_on_canvas(self.canvas)
                    return
                if hit == 'rot':
                    # start rotation mode
                    self.sep_mode = 'rotate'
                    self.rotation_handle_active = 'rot'
                    self.drag_start = (x,y)
                    # ensure angle box shows immediately
                    sep.selected = True
                    sep._draw_angle_box(self.canvas)
                elif hit == "reset":
                    sep.reset_angle()
                    sep.draw_on_canvas(self.canvas)
                    return

        # check top/bot handles
        for sep in reversed(self.separators):
            hx1, hy1 = sep.top_handle()
            hx2, hy2 = sep.bot_handle()
            if (x - hx1)**2 + (y - hy1)**2 <= (sep.HANDLE_R + 4)**2:
                self._select_separator(sep)
                self.sep_mode = 'move_top'
                self.drag_start = (x,y)
                return
            if (x - hx2)**2 + (y - hy2)**2 <= (sep.HANDLE_R + 4)**2:
                self._select_separator(sep)
                self.sep_mode = 'move_bot'
                self.drag_start = (x,y)
                return
        # line proximity to move entire separator
        for sep in reversed(self.separators):
            if sep.distance_to_line(x,y) < 8:
                self._select_separator(sep)
                self.sep_mode = 'move_line'
                # store offset so the center follows mouse nicely
                self.sep_drag_offset = (sep.cx - x, sep.cy - y)
                self.drag_start = (x,y)
                return
        # deselect if clicking empty space
        self._deselect_separator()

        # crop edges / inside
        edge = self._detect_edge_at(x,y)
        if self.crop_disp and edge:
            self.resizing = True
            self.resize_edge = edge
            self.rect_before = tuple(self.crop_disp)
            self.drag_start = (x,y)
            return
        if self.crop_disp and self._point_in_rect(x,y,self.crop_disp):
            self.dragging = True
            self.rect_before = tuple(self.crop_disp)
            self.drag_start = (x,y)
            return
        # start new crop
        self.dragging = True
        self.rect_before = None
        self.drag_start = (x,y)
        self.crop_disp = (x,y,x,y)
        self._update_crop_orig_from_disp()
        self.update_auto_crop_state()
        if hasattr(self, "show_crop_var") and not self.show_crop_var.get():
            self.show_crop_var.set(True)
            self.update_auto_crop_state()
        self.redraw()

    def canvas_move(self, event):
        x, y = event.x, event.y
        # separator interactions
        if self.sep_mode == 'move_top' and self.selected_sep:
            self.selected_sep.set_top_handle(x, y)
            self._clamp_selected_separator_to_display()
            self.redraw()
            return
        if self.sep_mode == 'move_bot' and self.selected_sep:
            self.selected_sep.set_bot_handle(x, y)
            self._clamp_selected_separator_to_display()
            self.redraw()
            return
        if self.sep_mode == 'move_line' and self.selected_sep:
            ox, oy = self.sep_drag_offset or (0,0)
            new_cx = x + ox
            desired_center_y = y + (self.sep_drag_offset[1] if self.sep_drag_offset else 0)
            prev_center_y = self.selected_sep.cy
            dy = desired_center_y - prev_center_y
            dx = new_cx - self.selected_sep.cx
            self.selected_sep.move_by(dx, dy)
            self._clamp_selected_separator_to_display()
            self.redraw()
            return

        if self.sep_mode == 'rotate' and self.selected_sep:
            # compute angle towards mouse relative to separator center.
            # angle = atan2(dy, dx) - pi/2  (keeps angle=0 vertical)
            dx = x - self.selected_sep.cx
            dy = y - self.selected_sep.cy
            if abs(dx) < 1e-9 and abs(dy) < 1e-9:
                return
            raw_angle = math.atan2(dy, dx) - math.pi / 2.0
            # check ctrl pressed (event.state): in Tkinter, control bit often 0x0004
            ctrl_pressed = (event.state & 0x0004) != 0
            if ctrl_pressed:
                step = math.radians(5.0)
                snapped = round(raw_angle / step) * step
                self.selected_sep.angle = snapped
            else:
                self.selected_sep.angle = raw_angle
            # update angle display (white box with black text) and keep it visible
            self.selected_sep.selected = True
            self.selected_sep._draw_angle_box(self.canvas)
            self._clamp_selected_separator_to_display()
            self.redraw()
            return

        # crop interactions
        if self.resizing and self.rect_before:
            x1,y1,x2,y2 = self.rect_before
            nx1, ny1, nx2, ny2 = x1,y1,x2,y2
            if 'left' in self.resize_edge:
                nx1 = min(x, x2 - 5)
            if 'right' in self.resize_edge:
                nx2 = max(x, x1 + 5)
            if 'top' in self.resize_edge:
                ny1 = min(y, y2 - 5)
            if 'bottom' in self.resize_edge:
                ny2 = max(y, y1 + 5)
            self.crop_disp = (nx1, ny1, nx2, ny2)
            self._update_crop_orig_from_disp()
            self.redraw()
            return
        if self.dragging and self.rect_before:
            dx = x - self.drag_start[0]; dy = y - self.drag_start[1]
            x1,y1,x2,y2 = self.rect_before
            self.crop_disp = (x1+dx, y1+dy, x2+dx, y2+dy)
            self._update_crop_orig_from_disp()
            self.redraw()
            return
        if self.dragging and not self.rect_before:
            x0,y0 = self.drag_start
            self.crop_disp = (min(x0,x), min(y0,y), max(x0,x), max(y0,y))
            self._update_crop_orig_from_disp()
            self.redraw()

    def canvas_up(self, event):
        # finalize sep operations
        if self.sep_mode in ('move_top','move_bot','move_line','rotate'):
            # angle display remains visible as long as separator is selected
            try:
                # remove transient angle display tag if any leftover
                self.canvas.delete("angle_display")
            except Exception:
                pass
            self.sep_mode = None
            self.sep_drag_offset = None
            self.rotation_handle_active = None
            self.drag_start = None
            self._clamp_selected_separator_to_display()
            self.redraw()
            return
        # finalize crop
        self.dragging = False
        self.resizing = False
        self.resize_edge = None
        self.rect_before = None
        self.drag_start = None
        if self.crop_disp:
            self._update_crop_orig_from_disp()
            self.update_auto_crop_state()
            # when crop changed, update separators' length to match new display size
            self._update_separators_length()
        self.redraw()

    def canvas_motion(self, event):
        x, y = event.x, event.y
        # cursor logic (show rotation cursor when over rot handle/button)
        for sep in reversed(self.separators):
            hit = sep.hit_test_rot_handle(x, y)
            if hit is not None:
                # change cursor depending on hit
                if hit == 'rot':
                    self.canvas.config(cursor='exchange')
                    return
                if hit == 'button':
                    self.canvas.config(cursor='hand2')
                    return
                if hit == 'reset':
                    self.canvas.config(cursor='hand2')
                    return
            hx1, hy1 = sep.top_handle()
            hx2, hy2 = sep.bot_handle()
            if (x - hx1)**2 + (y - hy1)**2 <= (sep.HANDLE_R + 4)**2 or (x - hx2)**2 + (y - hy2)**2 <= (sep.HANDLE_R + 4)**2:
                self.canvas.config(cursor='exchange')
                return
            if sep.distance_to_line(x,y) < 8:
                self.canvas.config(cursor='fleur')
                return
        edge = self._detect_edge_at(x,y)
        if edge:
            if edge in ('left','right'): self.canvas.config(cursor='sb_h_double_arrow')
            elif edge in ('top','bottom'): self.canvas.config(cursor='sb_v_double_arrow')
            else: self.canvas.config(cursor='top_left_corner')
            return
        if self.crop_disp and self._point_in_rect(x,y,self.crop_disp):
            self.canvas.config(cursor='fleur'); return
        self.canvas.config(cursor='cross')

    # -------------------------
    # crop helpers
    # -------------------------
    def _detect_edge_at(self, x, y):
        if not self.crop_disp: return None
        x1,y1,x2,y2 = self.crop_disp
        s = 8
        edges=[]
        if abs(x-x1)<=s and y1-s<=y<=y2+s: edges.append('left')
        if abs(x-x2)<=s and y1-s<=y<=y2+s: edges.append('right')
        if abs(y-y1)<=s and x1-s<=x<=x2+s: edges.append('top')
        if abs(y-y2)<=s and x1-s<=x<=x2+s: edges.append('bottom')
        return '-'.join(edges) if edges else None

    def _point_in_rect(self, x, y, rect):
        x1,y1,x2,y2 = rect
        return x1<=x<=x2 and y1<=y<=y2

    def _update_crop_orig_from_disp(self):
        """
        Aktualisiert self.crop_orig (Koordinaten im Originalbild)
        anhand von self.crop_disp (Display-Koordinaten).
        Nutzt exakte Skalierung basierend auf aktuellem display_image.
        """
        if not self.crop_disp or not self.display_image or not self.base_image:
            return

        dw, dh = self.display_image.size
        ow, oh = self.base_image.size
        sx, sy = ow / dw, oh / dh  # exakte Skalierungsfaktoren

        x1, y1, x2, y2 = self.crop_disp

        # Clamping in Display-Koordinaten
        x1 = max(0, min(x1, dw - 1))
        x2 = max(1, min(x2, dw))
        y1 = max(0, min(y1, dh - 1))
        y2 = max(1, min(y2, dh))

        # exakte Umrechnung auf Original-Koordinaten
        ox1 = int(round(x1 * sx))
        oy1 = int(round(y1 * sy))
        ox2 = int(round(x2 * sx))
        oy2 = int(round(y2 * sy))

        # Begrenzen auf Originalbildgröße
        ox1 = max(0, min(ox1, ow - 2))
        oy1 = max(0, min(oy1, oh - 2))
        ox2 = max(ox1 + 2, min(ox2, ow))
        oy2 = max(oy1 + 2, min(oy2, oh))

        self.crop_orig = (ox1, oy1, ox2, oy2)

    def orig_to_display(self, orig):
        if not orig or not self.display_image or not self.base_image: return None
        dw, dh = self.display_image.size
        ow, oh = self.base_image.size
        sx, sy = dw/ow, dh/oh
        ox1,oy1,ox2,oy2 = orig
        return (int(ox1*sx), int(oy1*sy), int(ox2*sx), int(oy2*sy))

    # -------------------------
    # separator management
    # -------------------------
    def add_vertical_separator(self):
        # create separator centered in display image area; length = min(dw,dh) * factor
        dw = max(200, self.canvas.winfo_width())
        dh = max(200, self.canvas.winfo_height())
        L = min(dw, dh) * 0.9  # shorter baseline length (90% of short side)
        sep = Separator(cx=dw/2.0, cy=dh/2.0, angle=0.0, length=L)
        self.separators.append(sep)
        self._select_separator(sep)
        self.redraw()

    def remove_selected_separator(self):
        if self.selected_sep and self.selected_sep in self.separators:
            # clean up any angle display tags
            try:
                self.canvas.delete(self.selected_sep.angle_box_tag)
                self.canvas.delete(self.selected_sep.angle_text_tag)
            except Exception:
                pass
            # remove rotating texts if any
            self.selected_sep.delete_rot_texts(self.canvas)
            self.separators.remove(self.selected_sep)
            self.selected_sep = None
            self.redraw()

    def toggle_separator(self):
        """Aktiviert oder entfernt den Trennbalken."""
        if self.show_separator_var.get():
            # Wenn aktiviert, füge einen neuen Separator hinzu (wenn keiner existiert)
            if not self.separators:
                dw = max(200, self.canvas.winfo_width())
                dh = max(200, self.canvas.winfo_height())
                L = min(dw, dh) * 0.9
                sep = Separator(cx=dw / 2.0, cy=dh / 2.0, angle=0.0, length=L)
                self.separators.append(sep)
                self._select_separator(sep)
                print("[Trennbalken aktiviert]")
        else:
            # Wenn deaktiviert, entferne alle Separatoren
            if self.separators:
                for sep in list(self.separators):
                    sep.delete_rot_texts(self.canvas)
                self.separators.clear()
                self.selected_sep = None
                print("[Trennbalken deaktiviert]")
        self.redraw()

    def toggle_crop_area(self):
        """Zeigt oder versteckt den Crop-Bereich."""
        if self.show_crop_var.get():
            if not self.crop_disp and self.display_image:
                dw, dh = self.display_image.size
                margin = 0.05
                self.crop_disp = (dw * margin, dh * margin, dw * (1 - margin), dh * (1 - margin))
                self._update_crop_orig_from_disp()
            # Wenn jetzt crop_orig gesetzt ist, initialisiere die reference_crop als feste Vorlage.
            if self.crop_orig:
                self.reference_crop = tuple(int(v) for v in self.crop_orig)
            print("[Crop-Bereich aktiviert]")

        else:
            # Wenn deaktiviert, Crop-Bereich entfernen
            self.crop_disp = None
            self.crop_orig = None
            print("[Crop-Bereich deaktiviert]")
        self.update_auto_crop_state()
        self.redraw()

    def _select_separator(self, sep):
        for s in self.separators:
            s.selected = (s is sep)
        self.selected_sep = sep
        # ensure angle box visible immediately when selected
        if self.selected_sep:
            self.selected_sep._draw_angle_box(self.canvas)
        self.redraw()

    def _deselect_separator(self):
        if self.selected_sep:
            for s in self.separators:
                s.selected = False
            # remove rot text tags for the previously selected
            self.selected_sep.delete_rot_texts(self.canvas)
            # remove angle box
            try:
                self.canvas.delete(self.selected_sep.angle_box_tag)
                self.canvas.delete(self.selected_sep.angle_text_tag)
            except Exception:
                pass
            self.selected_sep = None
            self.redraw()

    def _clamp_selected_separator_to_display(self):
        # ensure selected separator center stays inside display area (giving endpoints visible)
        if not self.selected_sep or not self.display_image:
            return
        dw, dh = self.display_image.size
        self.selected_sep.clamp_to_bounds(0, 0, dw, dh)

    def _update_separators_length(self):
        # set separators' length equal to min(display width, height) * factor
        if not self.display_image:
            return
        dw, dh = self.display_image.size
        L = min(dw, dh) * 0.9
        for sep in self.separators:
            sep.length = float(L)
            sep.clamp_to_bounds(0, 0, dw, dh)

    # -------------------------
    # AutoCrop: dynamic per image (feature matching + affine)
    # -------------------------
    def auto_adjust_crop(self, path, init_crop=None):
        """
        Präzise Auto-Crop-Funktion basierend auf Template-Matching.
        Der Crop-Bereich bleibt in seiner Größe fix und wird nur verschoben,
        um dem Buch (oder einem markanten Bereich) im neuen Bild zu folgen.
        """
        import cv2, numpy as np, os

        if not CV2_AVAILABLE:
            print("⚠️ OpenCV nicht verfügbar – kein Auto-Crop.")
            return init_crop or self.crop_orig

        if init_crop is None:
            init_crop = self.crop_orig
        if init_crop is None:
            print("❌ Kein initialer Crop vorhanden.")
            return None

        # Wenn keine Referenz gespeichert, setze sie einmalig
        if self.reference_crop is None:
            self.reference_crop = tuple(int(v) for v in init_crop)
            self.reference_image = cv2.imread(self.image_paths[self.current_index])
            print("[INIT] Referenz-Crop gesetzt.")
            return init_crop

        # Template aus der Referenz extrahieren
        try:
            ref_img = getattr(self, "reference_image", None)
            if ref_img is None:
                print("⚠️ Keine Referenz-Bildvorlage gefunden, setze neu.")
                self.reference_image = cv2.imread(self.image_paths[0])
                ref_img = self.reference_image

            rx1, ry1, rx2, ry2 = self.reference_crop
            template = ref_img[ry1:ry2, rx1:rx2]
            if template is None or template.size == 0:
                print("❌ Leeres Template!")
                return init_crop

            # Neues Bild laden
            img = cv2.imread(path)
            if img is None:
                print(f"❌ Bild konnte nicht geladen werden: {path}")
                return init_crop

            gray_img = cv2.cvtColor(img, cv2.COLOR_BGR2GRAY)
            gray_template = cv2.cvtColor(template, cv2.COLOR_BGR2GRAY)

            # Template-Matching (korrelativ)
            result = cv2.matchTemplate(gray_img, gray_template, cv2.TM_CCOEFF_NORMED)
            _, max_val, _, max_loc = cv2.minMaxLoc(result)
            (best_x, best_y) = max_loc

            # Falls Trefferwert zu niedrig, keine Bewegung
            if max_val < 0.4:
                print("⚠️ Niedrige Übereinstimmung, behalte alten Crop.")
                return init_crop

            # Crop-Position anpassen
            crop_w = rx2 - rx1
            crop_h = ry2 - ry1
            new_x1 = int(best_x)
            new_y1 = int(best_y)
            new_x2 = new_x1 + crop_w
            new_y2 = new_y1 + crop_h

            # Sicherheit: im Bild halten
            h, w = gray_img.shape
            new_x1 = max(0, min(new_x1, w - crop_w))
            new_y1 = max(0, min(new_y1, h - crop_h))
            new_x2 = new_x1 + crop_w
            new_y2 = new_y1 + crop_h

            new_crop = (new_x1, new_y1, new_x2, new_y2)
            self.last_crop = new_crop

            # Anzeige aktualisieren
            try:
                self.crop_orig = new_crop
                self.crop_disp = self.orig_to_display(new_crop)
            except Exception:
                pass

            return new_crop

        except Exception as e:
            print("❌ Auto-Crop Fehler:", e)
            return init_crop

    # -------------------------
    # Segment computation & saving
    # -------------------------
    def compute_segments_for_crop(self, crop_area):
        """
        Compute polygonal segments (in original image coords) produced by separators intersecting crop rect.
        """
        if not crop_area:
            return []
        ox1,oy1,ox2,oy2 = crop_area
        rect_poly = [(ox1,oy1),(ox2,oy1),(ox2,oy2),(ox1,oy2)]
        if not self.separators:
            return [rect_poly]
        if not self.display_image or not self.base_image:
            return [rect_poly]
        dw, dh = self.display_image.size
        ow, oh = self.base_image.size
        sx, sy = ow/dw, oh/dh
        entries = []
        for sep in self.separators:
            # Endpunkte im Display holen
            x1d, y1d, x2d, y2d = sep.endpoints()
            # In Originalkoordinaten umrechnen
            x1 = x1d * sx;
            y1 = y1d * sy
            x2 = x2d * sx;
            y2 = y2d * sy

            # Linienrichtungsvektor und dazu senkrechte Normale
            vx = x2 - x1
            vy = y2 - y1
            nx = -vy
            ny = vx

            # Normalisieren (numerisch stabil)
            norm = math.hypot(nx, ny)
            if norm < 1e-12:
                continue
            nx /= norm
            ny /= norm

            # Geradengleichung: nx*x + ny*y + c = 0; Punkt (x1,y1) liegt auf der Linie
            c = - (nx * x1 + ny * y1)
            d = -c  # nur zum Sortieren bei mehreren parallelen Linien

            entries.append((d, nx, ny, c))

        entries.sort(key=lambda e: e[0])
        segments = []
        N = len(entries)
        for i in range(N+1):
            poly = rect_poly[:]
            if i == 0:
                a,b,c = entries[0][1], entries[0][2], entries[0][3]
                poly = clip_polygon_halfplane(poly, -a, -b, -c)
            elif i == N:
                a,b,c = entries[-1][1], entries[-1][2], entries[-1][3]
                poly = clip_polygon_halfplane(poly, a, b, c)
            else:
                a1,b1,c1 = entries[i-1][1], entries[i-1][2], entries[i-1][3]
                a2,b2,c2 = entries[i][1], entries[i][2], entries[i][3]
                poly = clip_polygon_halfplane(poly, a1, b1, c1)
                poly = clip_polygon_halfplane(poly, -a2, -b2, -c2)
            if polygon_area(poly) > 1.0:
                segments.append(poly)
            else:
                segments.append([])
        return segments

    def save_segments(self, orig_path, crop_area, segments_polygons=None, ext=None, fmt=None):
        import os
        from PIL import Image, ImageTk, ImageDraw

        # Prüfe, ob das aktuelle Bild croppen oder trennen darf (laut Häkchen)
        states = self.image_states.get(orig_path, {"crop": True, "trennen": False})
        do_crop = states.get("crop", False)
        do_trennen = states.get("trennen", False)

        # Wenn weder Crop noch Trennen aktiviert ist → abbrechen
        if not do_crop and not do_trennen:
            print(f"[SKIP] {os.path.basename(orig_path)} – kein Häkchen aktiv.")
            return []

        # --- Format aus GUI auslesen ---
        # --- Formatauswahl aus GUI (Mehrfachauswahl möglich) ---
        formats_to_save = []


        if hasattr(self, "format_vars"):  # mehrere Checkboxen
            for fmt_name, var in self.format_vars.items():
                if var.get():
                    formats_to_save.append(fmt_name.upper())

        elif hasattr(self, "format_var"):  # nur ein Radiobutton
            formats_to_save = [self.format_var.get().upper()]

        if not formats_to_save:
            formats_to_save = ["JPEG"]  # Fallback

        # Dateiendungs-Map
        ext_map = {
            "JPEG": "jpg", "JPG": "jpg",
            "PNG": "png",
            "TIFF": "tiff", "TIF": "tiff",
            "BMP": "bmp",
            "PDF": "pdf"
        }

        """
        Korrigierte Speicherung:
        - Wenn keine Separatoren (self.separators leer): Nur Crop -> Crop-Ordner/<base>_crop_edit_<n>.<ext>
        - Wenn Separatoren vorhanden: Nur Teile -> Trenn-Ordner/<base>_teil_<global_n>.<ext>
          (global_n ist fortlaufend über alle bereits vorhandenen Teil-Dateien im Trenn-Ordner)
        """
        import os, re, math
        from PIL import Image

        saved_files = []

        try:
            img = Image.open(orig_path).convert("RGB")
        except Exception as e:
            print("Fehler beim Öffnen:", e)
            return []

        # crop area -> PIL crop
        ox1, oy1, ox2, oy2 = crop_area
        crop = img.crop((ox1, oy1, ox2, oy2))
        base_name = os.path.splitext(os.path.basename(orig_path))[0]

        # output root (user selected oder original-ordner)
        root_outdir = getattr(self, "output_folder", os.path.dirname(orig_path))
        if not root_outdir:
            root_outdir = os.path.dirname(orig_path)
        os.makedirs(root_outdir, exist_ok=True)

        # --- Entscheidung anhand Häkchen ---
        # Crop erlaubt? → Crop-Ordner
        # Trennen erlaubt? → Trenn-Ordner
        separators_active = do_trennen and bool(getattr(self, "separators", None) and len(self.separators) > 0)


        # -----------------------
        # CASE A: Nur Crop (keine Separatoren aktiv)
        # -----------------------
        if not separators_active:
            base_crop_dir = os.path.join(root_outdir, "Crop-Ordner")
            os.makedirs(base_crop_dir, exist_ok=True)

            # fortlaufende Nummer finden (Dateiname unabhängig vom Format)
            n = 1
            while True:
                test_name = f"{base_name}_crop_edit_{n}"
                exists_any = any(
                    os.path.exists(os.path.join(base_crop_dir, fmt, f"{test_name}.{ext_map.get(fmt, fmt.lower())}"))
                    for fmt in formats_to_save
                    if os.path.isdir(os.path.join(base_crop_dir, fmt))
                )
                if not exists_any:
                    break
                n += 1

            # --- Speichern in allen aktivierten Formaten ---
            for fmt in formats_to_save:
                ext = ext_map.get(fmt, fmt.lower())

                # Format-Unterordner
                fmt_dir = os.path.join(base_crop_dir, fmt)
                os.makedirs(fmt_dir, exist_ok=True)

                outpath = os.path.join(fmt_dir, f"{base_name}_crop_edit_{n}.{ext}")
                try:
                    if fmt == "PDF":
                        crop.convert("RGB").save(outpath, format="PDF")
                    elif fmt == "PNG":
                        crop.convert("RGBA").save(outpath, format="PNG")
                    else:
                        crop.convert("RGB").save(outpath, format=fmt)

                    saved_files.append(outpath)
                    print(f"[GESPEICHERT - CROP {fmt}] {outpath}")
                except Exception as e:
                    print(f"Fehler beim Speichern ({fmt}): {e}")

            return saved_files

        # -----------------------
        # CASE B: Separatoren aktiv -> Trennmodus
        # - Kein Gesamtcrop speichern
        # - Teile direkt in Trenn-Ordner speichern, global fortlaufend nummeriert
        # -----------------------
        base_trenn_dir = os.path.join(root_outdir, "Trenn-Ordner")
        os.makedirs(base_trenn_dir, exist_ok=True)

        # Bestimme nächsten globalen Index in Trenn-Ordner, unabhängig von base_name.
        # Wir suchen nach Dateien mit Pattern "..._teil_<num>.<ext>" (für beliebige ext),
        # und nehmen max(num)+1. Robust: prüft alle Dateien mit "_teil_<digits>".
        def next_global_trenn_index(folder):
            max_n = 0
            pat = re.compile(r"_teil_(\d+)(?:\.[^.]+)?$", re.IGNORECASE)
            try:
                for fn in os.listdir(folder):
                    m = pat.search(fn)
                    if m:
                        try:
                            v = int(m.group(1))
                            if v > max_n:
                                max_n = v
                        except ValueError:
                            continue
            except FileNotFoundError:
                return 1
            return max_n + 1

        current_index = next_global_trenn_index(base_trenn_dir)

        # segments_polygons may include many polygons; iterate and save valid ones
        for poly in (segments_polygons or []):
            if not poly or polygon_area(poly) < 1.0:
                continue

            # Polygon-Koordinaten relativ zum Crop-Bereich
            local = [(x - ox1, y - oy1) for (x, y) in poly]

            # Erstelle eine leere RGBA-Fläche in voller Crop-Größe
            full_w, full_h = crop.size
            full_rgba = Image.new("RGBA", (full_w, full_h), (0, 0, 0, 0))

            # Maske für dieses Polygon (volle Größe!)
            mask = Image.new("L", (full_w, full_h), 0)
            draw = ImageDraw.Draw(mask)
            draw.polygon(local, fill=255)

            # Crop-Bereich einfügen, aber nur dort, wo Maske 255 ist
            full_rgba.paste(crop.convert("RGBA"), (0, 0), mask)

            # => alle Teilbilder gleich groß (full_w × full_h)

            for fmt in formats_to_save:
                ext = ext_map.get(fmt, fmt.lower())
                fmt_dir = os.path.join(base_trenn_dir, fmt)
                os.makedirs(fmt_dir, exist_ok=True)

                fname = f"{base_name}_teil_{current_index}.{ext}"
                outpath = os.path.join(fmt_dir, fname)

                try:
                    if fmt == "PDF":
                        # PDF braucht weißen Hintergrund
                        bg = Image.new("RGB", (full_w, full_h), (255, 255, 255))
                        bg.paste(full_rgba, (0, 0), full_rgba.split()[-1])
                        bg.save(outpath, format="PDF")
                    elif fmt == "PNG":
                        full_rgba.save(outpath, format="PNG")
                    elif fmt in ("JPEG", "JPG", "BMP", "TIFF"):
                        bg = Image.new("RGB", (full_w, full_h), (255, 255, 255))
                        bg.paste(full_rgba, (0, 0), full_rgba.split()[-1])
                        bg.save(outpath, format=fmt)
                    else:
                        full_rgba.save(outpath)

                    saved_files.append(outpath)
                    print(f"[GESPEICHERT - TEIL {fmt}] {outpath}")
                except Exception as e:
                    print(f"Fehler beim Speichern ({fmt}): {e}")

            current_index += 1

        return saved_files

    # -------------------------
    # Crop single/all
    # -------------------------
    def crop_single(self):
        if not self.image_paths:
            return
        if not self.crop_orig:
            messagebox.showwarning("Fehler", "Kein Crop-Bereich festgelegt.")
            return
        path = self.image_paths[self.current_index]
        # ensure we have a baseline crop before attempting auto-adjust
        if not self.crop_orig and self.auto_crop_var.get():
            messagebox.showwarning("Auto-Crop",
                                   "Kein vorhandener Crop als Referenz. Bitte zuerst 'Crop-Bereich' aktivieren und Crop setzen.")
            return
        adj_crop = self.auto_adjust_crop(path, self.crop_orig) if self.auto_crop_var.get() else self.crop_orig

        segments = self.compute_segments_for_crop(adj_crop)
        saved = self.save_segments(path, adj_crop, segments)
        messagebox.showinfo("Fertig", f"{len(saved)} Teile gespeichert:\n" + "\n".join(os.path.basename(s) for s in saved))

    def crop_all_threaded(self):
        if not self.image_paths:
            return
        t = threading.Thread(target=self.crop_all)
        t.daemon = True
        t.start()

    def crop_all(self):
        total = len(self.image_paths)
        self.progress_var.set(0)
        if not self.crop_orig:
            messagebox.showwarning("Fehler", "Kein Crop-Bereich festgelegt.")
            return
        for i, path in enumerate(self.image_paths):
            # Prüfe pro Bild, was erlaubt ist
            state = self.image_states.get(path, {"crop": True, "trennen": False})
            do_crop = state.get("crop", False)
            do_trennen = state.get("trennen", False)

            # Wenn weder Crop noch Trennen aktiviert ist → überspringen
            if not do_crop and not do_trennen:
                print(f"[SKIP] {os.path.basename(path)} – kein Häkchen aktiv.")
                continue

            # Stopp-Flag prüfen
            if self.stop_flag.is_set():
                print("[STOP] Crop-Vorgang wurde gestoppt.")
                break

            self.current_index = i

            # Prüfe ob Auto-Crop erlaubt
            if not self.crop_orig and self.auto_crop_var.get():
                messagebox.showwarning("Auto-Crop",
                                       "Kein vorhandener Crop als Referenz. Bitte zuerst 'Crop-Bereich' aktivieren und Crop setzen.")
                return

            # Berechne Crop
            adj_crop = self.auto_adjust_crop(path, self.crop_orig) if self.auto_crop_var.get() else self.crop_orig

            # Berechne Segmente, falls Trennen aktiv
            segments = self.compute_segments_for_crop(adj_crop) if do_trennen else [None]

            # Speichern (nur, wenn mindestens eine Option aktiv ist)
            self.save_segments(path, adj_crop, segments)

            self.progress_var.set((i + 1) / total * 100.0)
            self.progress.update_idletasks()

        # Nach Ende oder Abbruch Fortschrittsbalken zurücksetzen
        self.progress_var.set(0)
        self.stop_flag.clear()
        messagebox.showinfo("Fertig", f"Alle {i + 1 if not self.stop_flag.is_set() else i} Bilder verarbeitet.")

    # -------------------------
    # Angle display (kept for compatibility - not used; angle box drawn by Separator)
    # -------------------------
    def _update_angle_display(self, event, sep):
        """Legacy helper — kept but separators draw their own angle box."""
        try:
            self.canvas.delete("angle_display")
        except Exception:
            pass
        angle_deg = (math.degrees(sep.angle)) % 360.0
        text = f"{angle_deg:6.1f}°"
        # small transient display near mouse (not used as main display)
        self.canvas.create_text(event.x + 30, event.y - 10, text=text, fill="yellow",
                                font=("Consolas", 13, "bold"), tags="angle_display")

    # -------------------------
    # Mousewheel zoom
    # -------------------------
    def on_mousewheel(self, event):
        if not self.base_image:
            return
        factor = 1.1 if event.delta > 0 else 0.9
        self.zoom *= factor
        self.zoom = max(0.2, min(5.0, self.zoom))
        self.display_image = self.get_display_image()
        self._update_crop_orig_from_disp()
        self._update_separators_length()
        self.redraw()

    def on_mousewheel_linux(self, event):
        if event.num == 4:
            event.delta = 120
        elif event.num == 5:
            event.delta = -120
        self.on_mousewheel(event)

    # -------------------------
    # Misc handlers
    # -------------------------
    def on_escape(self, event=None):
        # clear crop and deselect
        self.crop_disp = None
        self.crop_orig = None
        self.update_auto_crop_state()
        self._deselect_separator()
        self.redraw()

    def on_delete_key(self, event=None):
        # Wenn Separator ausgewählt ist -> löschen
        if self.selected_sep:
            self.remove_selected_separator()
            return

        # Ausgewählte Treeview-Zeilen entfernen
        sel = self.tree.selection()
        if not sel:
            return
        names = [self.tree.item(i, "values")[0] for i in sel]
        paths_to_remove = [p for p in self.image_paths if os.path.basename(p) in names]

        # aus Listen löschen
        for p in paths_to_remove:
            if p in self.image_paths:
                self.image_paths.remove(p)
            self.image_states.pop(p, None)

        self.update_tree()
        if self.current_index >= len(self.image_paths):
            self.current_index = max(0, len(self.image_paths) - 1)
        self.load_current_image()

    def on_configure(self, event):
        if self.base_image:
            self.display_image = self.get_display_image()
            if self.crop_orig:
                self.crop_disp = self.orig_to_display(self.crop_orig)
            self._update_separators_length()
            self.redraw()


# -------------------------
# main
# -------------------------
if __name__ == "__main__":
    try:
        if DND_AVAILABLE:
            from tkinterdnd2 import TkinterDnD
            root = TkinterDnD.Tk()
            root.title("Crop + Vertical Rotatable Separators")
            tb.Style("cyborg")
        else:
            root = tb.Window(themename="cyborg")

        app = ImageCropSplitterApp(root)
        root.state('zoomed')
        root.mainloop()
    except Exception as e:
        print("Fehler beim Start:", e)


