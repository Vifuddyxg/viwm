#define _POSIX_C_SOURCE 200809L

#include <X11/Xlib.h>
#include <X11/XKBlib.h>
#include <X11/Xatom.h>
#include <X11/cursorfont.h>
#include <X11/XF86keysym.h>
#include <X11/Xutil.h>
#include <X11/keysym.h>
#include <X11/extensions/Xinerama.h>
#include <signal.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <strings.h>
#include <time.h>
#include <unistd.h>

#define MOD          Mod4Mask
#define MAXBINDS     48
#define MAXMODEBINDS 24
#define MAXCMDS      16
#define MAXRULES     32
#define MAXMONS       8
#define MAXWS         9
#define MAXAUTOSTART 8
#define CMDLINE_MAX 256

typedef struct Node Node;
struct Node {
    int leaf, floating, horiz;
    int fullscreen;
    int real_fullscreen;
    int ignore_unmap;
    float ratio;
    Node *a, *b, *par;
    Window win;
    int x, y, w, h;
};

typedef struct {
    unsigned int mod;
    KeyCode code;
    char action[256];
} ModBind;

typedef struct {
    KeySym sym;
    char action[256];
} ModeBind;

typedef struct {
    char name[64];
    char action[256];
} CmdBind;

typedef struct {
    char class_name[64];
    char instance_name[64];
    char title[128];
    int set_floating;
    int floating;
    int workspace;
} Rule;

typedef struct {
    int x, y, w, h;
    int wx, wy, ww, wh;
    Node *tree[MAXWS], *focused[MAXWS];
    Window barwin;
} Mon;

typedef enum {
    BAR_TOP = 0,
    BAR_BOTTOM
} BarPosition;

typedef enum {
    MODE_INSERT = 0,
    MODE_NORMAL,
    MODE_COMMAND
} InputMode;

static int gap = 8, bw = 2, barh = 24;
static int barpadx = 10, baritemgap = 6, bartextpad = 8, barwsminw = 20;
static unsigned long cfocus = 0x5588ff, cnorm = 0x333333;
static unsigned long barbg = 0x111111, barfg = 0xeeeeee;
static unsigned long baraccentbg = 0x5588ff, baraccentfg = 0x111111;
static unsigned long barmutedfg = 0xaaaaaa;
static char term[128] = "st";
static char barfontname[128] = "9x15";
static char barleftcfg[128] = "workspaces";
static char barcentercfg[128] = "command";
static char barrightcfg[128] = "clock";
static BarPosition barpos = BAR_TOP;
static Display *dpy;
static Window root;
static int sw, sh;
static Mon mons[MAXMONS];
static int nmons = 1, curmon;
static int curws;
static Window wmcheckwin;
static ModBind modbinds[MAXBINDS];
static int nmodbinds;
static ModeBind normalbinds[MAXMODEBINDS];
static int nnormalbinds;
static CmdBind cmdbinds[MAXCMDS];
static int ncmdbinds;
static Rule rules[MAXRULES];
static int nrules;
static char autostart_cmds[MAXAUTOSTART][256];
static int nautostart;
static int modbind_limit = MAXBINDS;
static int normalbind_limit = MAXMODEBINDS;
static int cmd_limit = MAXCMDS;
static int autostart_limit = MAXAUTOSTART;
static GC bargc;
static XFontStruct *barfont;
static Cursor normalcursor;
static Cursor movecursor;
static Cursor resizecursor;
static InputMode mode = MODE_INSERT;
static int keyboard_grabbed;
static int running = 1;
static unsigned int numlockmask;
static Atom atom_net_active_window;
static Atom atom_net_client_list;
static Atom atom_net_current_desktop;
static Atom atom_net_number_of_desktops;
static Atom atom_net_supported;
static Atom atom_net_supporting_wm_check;
static Atom atom_utf8_string;
static Atom atom_net_wm_window_type;
static Atom atom_net_wm_window_type_dock;
static Atom atom_net_wm_window_type_dialog;
static Atom atom_net_wm_window_type_utility;
static Atom atom_net_wm_window_type_toolbar;
static Atom atom_net_wm_window_type_splash;
static Atom atom_net_wm_desktop;
static Atom atom_net_wm_state;
static Atom atom_net_wm_state_fullscreen;
static char cmdline[CMDLINE_MAX];
static int cmdline_len;
static char timestr[32];
static char batterystr[64];
static int last_clock_second = -1;
static int drag_mode;
static int drag_mon;
static int drag_ox, drag_oy;
static int drag_wx, drag_wy;
static int drag_ww, drag_wh;
static Node *drag_node;

static int xerr(Display *d, XErrorEvent *e) { (void)d; (void)e; return 0; }
static void drawbars(void);
static void update_clock(void);
static void update_battery(void);
static void setupbars(void);
static void enter_mode(InputMode newmode);
static Node *mon_focused(int mi);
static void showtree(Node *n);
static void spawn(const char *cmd);
static void initatoms(void);
static void apply_rules(Node *n, int *targetws);
static void update_client_list(void);
static void update_current_desktop(void);
static void update_number_of_desktops(void);
static void update_active_window(void);
static void set_window_desktop(Window win, int ws);
static void update_supported_atoms(void);
static void setup_wm_check(void);
static void reloadwm(void);
static void collect_leaves(Node *n, Node **list, int *count, int maxcount);
static unsigned long hcol(const char *s) {
    return strtoul(*s == '#' ? s + 1 : s, NULL, 16);
}

static char *ltrim(char *s) {
    while (*s == ' ' || *s == '\t') s++;
    return s;
}

static void rtrim(char *s) {
    size_t len = strlen(s);
    while (len && (s[len - 1] == '\n' || s[len - 1] == '\r' ||
                   s[len - 1] == ' ' || s[len - 1] == '\t')) {
        s[--len] = 0;
    }
}

static void copystr(char *dst, size_t dstsz, const char *src) {
    size_t n;
    if (!dstsz) return;
    if (!src) src = "";
    n = strlen(src);
    if (n >= dstsz) n = dstsz - 1;
    memcpy(dst, src, n);
    dst[n] = 0;
}

static const char *skip_command_prefix(const char *s) {
    return (s && s[0] == ':') ? s + 1 : s;
}

static KeySym parse_keysym_name(const char *name) {
    char lowered[64];
    size_t len;
    KeySym sym;

    if (!name || !*name) return NoSymbol;
    if (strcmp(name, " ") == 0) return XK_space;

    len = strlen(name);
    if (len >= sizeof lowered) len = sizeof lowered - 1;
    for (size_t i = 0; i < len; i++) {
        char c = name[i];
        lowered[i] = (c >= 'A' && c <= 'Z') ? (char)(c - 'A' + 'a') : c;
    }
    lowered[len] = 0;

    if (!strcmp(lowered, "space")) return XK_space;
    if (!strcmp(lowered, "return") || !strcmp(lowered, "enter")) return XK_Return;
    if (!strcmp(lowered, "escape") || !strcmp(lowered, "esc")) return XK_Escape;
    if (!strcmp(lowered, "page_up") || !strcmp(lowered, "pageup") || !strcmp(lowered, "prior"))
        return XK_Page_Up;
    if (!strcmp(lowered, "page_down") || !strcmp(lowered, "pagedown") || !strcmp(lowered, "next"))
        return XK_Page_Down;
    if (!strcmp(lowered, "left")) return XK_Left;
    if (!strcmp(lowered, "right")) return XK_Right;
    if (!strcmp(lowered, "up")) return XK_Up;
    if (!strcmp(lowered, "down")) return XK_Down;
    if (!strcmp(lowered, "tab")) return XK_Tab;
    if (!strcmp(lowered, "backspace")) return XK_BackSpace;
    if (!strcmp(lowered, "xf86audioraisevolume")) return XF86XK_AudioRaiseVolume;
    if (!strcmp(lowered, "xf86audiolowervolume")) return XF86XK_AudioLowerVolume;
    if (!strcmp(lowered, "xf86audiomute")) return XF86XK_AudioMute;
    if (!strcmp(lowered, "xf86audioplay")) return XF86XK_AudioPlay;
    if (!strcmp(lowered, "xf86audiopause")) return XF86XK_AudioPause;
    if (!strcmp(lowered, "xf86audionext")) return XF86XK_AudioNext;
    if (!strcmp(lowered, "xf86audioprev")) return XF86XK_AudioPrev;
    if (!strcmp(lowered, "xf86audiostop")) return XF86XK_AudioStop;
    if (!strcmp(lowered, "xf86monbrightnessup")) return XF86XK_MonBrightnessUp;
    if (!strcmp(lowered, "xf86monbrightnessdown")) return XF86XK_MonBrightnessDown;

    sym = XStringToKeysym(name);
    if (sym == NoSymbol) sym = XStringToKeysym(lowered);
    if (sym == NoSymbol && strlen(name) == 1) sym = (KeySym)(unsigned char)name[0];
    return sym;
}

static int textw(const char *s) {
    return s ? ((barfont && XTextWidth(barfont, s, (int)strlen(s))) ? XTextWidth(barfont, s, (int)strlen(s)) : (int)strlen(s) * 8) : 0;
}

static void build_mode_text(char *dst, size_t dstsz) {
    const char *label = mode == MODE_INSERT ? "INSERT" :
                        mode == MODE_NORMAL ? "NORMAL" : "COMMAND";
    snprintf(dst, dstsz, "%s", label);
}

static int clampi(int value, int minv, int maxv) {
    if (value < minv) return minv;
    if (value > maxv) return maxv;
    return value;
}

static int get_window_title(Window win, char *dst, size_t dstsz) {
    Atom net_wm_name = XInternAtom(dpy, "_NET_WM_NAME", False);
    Atom utf8_string = XInternAtom(dpy, "UTF8_STRING", False);
    XTextProperty prop;
    char **list = NULL;
    int count = 0;

    dst[0] = 0;
    if (XGetTextProperty(dpy, win, &prop, net_wm_name) && prop.value && prop.nitems > 0) {
        if (prop.encoding == utf8_string) {
            copystr(dst, dstsz, (char *)prop.value);
            XFree(prop.value);
            return dst[0] != 0;
        }
        if (XmbTextPropertyToTextList(dpy, &prop, &list, &count) >= Success && count > 0 && list && list[0]) {
            copystr(dst, dstsz, list[0]);
            XFreeStringList(list);
            XFree(prop.value);
            return dst[0] != 0;
        }
        XFree(prop.value);
    }

    if (XGetWMName(dpy, win, &prop) && prop.value && prop.nitems > 0) {
        if (XmbTextPropertyToTextList(dpy, &prop, &list, &count) >= Success && count > 0 && list && list[0]) {
            copystr(dst, dstsz, list[0]);
            XFreeStringList(list);
            XFree(prop.value);
            return dst[0] != 0;
        }
        XFree(prop.value);
    }
    return 0;
}

static int get_window_class(Window win, char *class_name, size_t class_sz,
    char *instance_name, size_t instance_sz)
{
    XClassHint hint;
    class_name[0] = 0;
    instance_name[0] = 0;
    if (!XGetClassHint(dpy, win, &hint)) return 0;
    if (hint.res_class) {
        copystr(class_name, class_sz, hint.res_class);
        XFree(hint.res_class);
    }
    if (hint.res_name) {
        copystr(instance_name, instance_sz, hint.res_name);
        XFree(hint.res_name);
    }
    return class_name[0] || instance_name[0];
}

static int window_has_atom(Window win, Atom prop, Atom value) {
    Atom actual_type;
    int actual_format;
    unsigned long nitems, bytes_after;
    Atom *atoms = NULL;
    int found = 0;
    if (XGetWindowProperty(dpy, win, prop, 0, 32, False, XA_ATOM,
            &actual_type, &actual_format, &nitems, &bytes_after,
            (unsigned char **)&atoms) != Success) return 0;
    if (actual_type == XA_ATOM && actual_format == 32 && atoms) {
        for (unsigned long i = 0; i < nitems; i++) {
            if (atoms[i] == value) {
                found = 1;
                break;
            }
        }
    }
    if (atoms) XFree(atoms);
    return found;
}

static void build_title_text(char *dst, size_t dstsz) {
    Node *n = mon_focused(curmon);
    dst[0] = 0;
    if (!n || !n->leaf) return;
    get_window_title(n->win, dst, dstsz);
}

static void build_clock_text(char *dst, size_t dstsz) {
    update_clock();
    snprintf(dst, dstsz, "%s", timestr[0] ? timestr : "--:--");
}

static void build_battery_text(char *dst, size_t dstsz) {
    update_battery();
    snprintf(dst, dstsz, "%s", batterystr);
}

static void update_clock(void) {
    time_t now = time(NULL);
    struct tm tm_now;
    localtime_r(&now, &tm_now);
    if (tm_now.tm_sec == last_clock_second) return;
    last_clock_second = tm_now.tm_sec;
    strftime(timestr, sizeof timestr, "%H:%M", &tm_now);
}

static void update_battery(void) {
    static time_t last_battery_update = 0;
    time_t now = time(NULL);
    const char *bases[] = {
        "/sys/class/power_supply/BAT0",
        "/sys/class/power_supply/BAT1",
        "/sys/class/power_supply/battery",
        NULL
    };
    char path[256], status[32], cap[32];
    FILE *f;

    if (last_battery_update && now - last_battery_update < 15) return;
    last_battery_update = now;
    batterystr[0] = 0;

    for (int i = 0; bases[i]; i++) {
        snprintf(path, sizeof path, "%s/capacity", bases[i]);
        f = fopen(path, "r");
        if (!f) continue;
        if (!fgets(cap, sizeof cap, f)) {
            fclose(f);
            continue;
        }
        fclose(f);
        rtrim(cap);

        snprintf(path, sizeof path, "%s/status", bases[i]);
        f = fopen(path, "r");
        if (f && fgets(status, sizeof status, f)) {
            fclose(f);
            rtrim(status);
        } else {
            if (f) fclose(f);
            status[0] = 0;
        }

        if (!strcasecmp(status, "Charging")) snprintf(batterystr, sizeof batterystr, "BAT+ %s%%", cap);
        else if (!strcasecmp(status, "Full")) snprintf(batterystr, sizeof batterystr, "BAT= %s%%", cap);
        else if (status[0]) snprintf(batterystr, sizeof batterystr, "BAT %s%%", cap);
        else snprintf(batterystr, sizeof batterystr, "BAT %s%%", cap);
        return;
    }
}

static int monforpt(int x, int y) {
    for (int i = 0; i < nmons; i++) {
        if (x >= mons[i].x && x < mons[i].x + mons[i].w &&
            y >= mons[i].y && y < mons[i].y + mons[i].h) return i;
    }
    return 0;
}

static Node *mon_tree(int mi) {
    return mons[mi].tree[curws];
}

static Node *mon_focused(int mi) {
    return mons[mi].focused[curws];
}

static Node *mon_tree_at(int mi, int ws) {
    return mons[mi].tree[ws];
}

static Node *mon_focused_at(int mi, int ws) {
    return mons[mi].focused[ws];
}

static void mon_setfocused(int mi, Node *n) {
    mons[mi].focused[curws] = n;
}

static void mon_settree_at(int mi, int ws, Node *n) {
    mons[mi].tree[ws] = n;
}

static void mon_setfocused_at(int mi, int ws, Node *n) {
    mons[mi].focused[ws] = n;
}

static Node *mkleaf(Window w) {
    Node *n = calloc(1, sizeof *n);
    n->leaf = 1;
    n->ratio = 0.5f;
    n->win = w;
    return n;
}

static int atom_in_window_property(Window win, Atom prop, Atom value) {
    return window_has_atom(win, prop, value);
}

static int window_is_dialog_like(Window win) {
    Window transient_for;
    if (XGetTransientForHint(dpy, win, &transient_for)) return 1;
    return atom_in_window_property(win, atom_net_wm_window_type, atom_net_wm_window_type_dialog) ||
           atom_in_window_property(win, atom_net_wm_window_type, atom_net_wm_window_type_utility) ||
           atom_in_window_property(win, atom_net_wm_window_type, atom_net_wm_window_type_toolbar) ||
           atom_in_window_property(win, atom_net_wm_window_type, atom_net_wm_window_type_splash);
}

static Node *findleaf(Node *n, Window w) {
    if (!n) return NULL;
    if (n->leaf) return n->win == w ? n : NULL;
    Node *r = findleaf(n->a, w);
    return r ? r : findleaf(n->b, w);
}

static Node *findleaf_any(Window w, int *out_mi, int *out_ws) {
    for (int mi = 0; mi < nmons; mi++) {
        for (int ws = 0; ws < MAXWS; ws++) {
            Node *n = findleaf(mon_tree_at(mi, ws), w);
            if (n) {
                if (out_mi) *out_mi = mi;
                if (out_ws) *out_ws = ws;
                return n;
            }
        }
    }
    return NULL;
}

static int monforwin(Window w) {
    for (int i = 0; i < nmons; i++) {
        if (findleaf(mon_tree(i), w)) return i;
    }
    return curmon;
}

static Node *firstleaf(Node *n) {
    while (n && !n->leaf) n = n->a;
    return n;
}

static Node *find_fullscreen_leaf(Node *n) {
    Node *r;
    if (!n) return NULL;
    if (n->leaf) return (n->real_fullscreen || n->fullscreen) ? n : NULL;
    r = find_fullscreen_leaf(n->a);
    return r ? r : find_fullscreen_leaf(n->b);
}

static Node *find_real_fullscreen_leaf(Node *n) {
    Node *r;
    if (!n) return NULL;
    if (n->leaf) return n->real_fullscreen ? n : NULL;
    r = find_real_fullscreen_leaf(n->a);
    return r ? r : find_real_fullscreen_leaf(n->b);
}

static int monitor_has_real_fullscreen(int mi) {
    return find_real_fullscreen_leaf(mon_tree(mi)) != NULL;
}

static void raise_bar_if_needed(int mi) {
    if (mons[mi].barwin && !monitor_has_real_fullscreen(mi)) XRaiseWindow(dpy, mons[mi].barwin);
}

static int workspace_has_windows(int ws) {
    for (int i = 0; i < nmons; i++) {
        if (mons[i].tree[ws]) return 1;
    }
    return 0;
}

static Node *nextleaf(int mi, Node *cur) {
    Node *tree = mon_tree(mi);
    if (!cur || !tree) return firstleaf(tree);
    Node *n = cur;
    while (n->par) {
        if (n->par->a == n) {
            Node *r = firstleaf(n->par->b);
            if (r) return r;
        }
        n = n->par;
    }
    return firstleaf(tree);
}

static Node *prevleaf(int mi, Node *cur) {
    Node *tree = mon_tree(mi);
    Node *prev = NULL;
    Node *n;
    if (!tree) return NULL;
    if (!cur) {
        n = firstleaf(tree);
        if (!n) return NULL;
        while ((n = nextleaf(mi, n)) && n != firstleaf(tree)) prev = n;
        return prev ? prev : firstleaf(tree);
    }
    n = firstleaf(tree);
    while (n) {
        if (n == cur) break;
        prev = n;
        n = nextleaf(mi, n);
        if (n == firstleaf(tree)) break;
    }
    if (prev) return prev;
    n = firstleaf(tree);
    prev = n;
    while ((n = nextleaf(mi, prev)) && n != firstleaf(tree)) prev = n;
    return prev;
}

static void swap_leaf_payload(Node *a, Node *b) {
    Window wtmp;
    int ftmp;
    int fstmp;
    if (!a || !b || a == b || !a->leaf || !b->leaf) return;
    wtmp = a->win;
    a->win = b->win;
    b->win = wtmp;
    ftmp = a->floating;
    a->floating = b->floating;
    b->floating = ftmp;
    fstmp = a->fullscreen;
    a->fullscreen = b->fullscreen;
    b->fullscreen = fstmp;
    fstmp = a->real_fullscreen;
    a->real_fullscreen = b->real_fullscreen;
    b->real_fullscreen = fstmp;
}

static void drawborder(Node *n, int focused) {
    XSetWindowBorderWidth(dpy, n->win, n->real_fullscreen ? 0 : bw);
    XSetWindowBorder(dpy, n->win, focused ? cfocus : cnorm);
}

static void raise_floating(Node *n) {
    if (!n) return;
    if (n->leaf) {
        if (n->floating) XRaiseWindow(dpy, n->win);
        return;
    }
    raise_floating(n->a);
    raise_floating(n->b);
}

static void unmap_managed(Node *n) {
    if (!n || !n->leaf) return;
    n->ignore_unmap++;
    XUnmapWindow(dpy, n->win);
}

static void show_only_leaf(Node *n, Node *target) {
    if (!n) return;
    if (n->leaf) {
        if (n == target) XMapRaised(dpy, n->win);
        else unmap_managed(n);
        return;
    }
    show_only_leaf(n->a, target);
    show_only_leaf(n->b, target);
}

static int has_tiled_leaf(Node *n) {
    if (!n) return 0;
    if (n->leaf) return !n->floating;
    return has_tiled_leaf(n->a) || has_tiled_leaf(n->b);
}

static void tilenode(Node *n, int x, int y, int w, int h, Node *foc) {
    if (!n) return;
    n->x = x;
    n->y = y;
    n->w = w;
    n->h = h;
    if (n->leaf) {
        drawborder(n, n == foc);
        if (n->fullscreen || n->real_fullscreen) {
            XMoveResizeWindow(dpy, n->win, x, y, w - 2 * bw, h - 2 * bw);
        } else if (!n->floating) {
            int tw = w - 2 * gap - 2 * bw;
            int th = h - 2 * gap - 2 * bw;
            if (tw < 1) tw = 1;
            if (th < 1) th = 1;
            XMoveResizeWindow(dpy, n->win, x + gap, y + gap, tw, th);
        }
        return;
    }
    if (!has_tiled_leaf(n->a) && has_tiled_leaf(n->b)) {
        tilenode(n->b, x, y, w, h, foc);
        return;
    }
    if (!has_tiled_leaf(n->b) && has_tiled_leaf(n->a)) {
        tilenode(n->a, x, y, w, h, foc);
        return;
    }
    if (!has_tiled_leaf(n->a) && !has_tiled_leaf(n->b)) return;
    if (n->horiz) {
        int wa = (int)(w * n->ratio);
        tilenode(n->a, x, y, wa, h, foc);
        tilenode(n->b, x + wa, y, w - wa, h, foc);
    } else {
        int ha = (int)(h * n->ratio);
        tilenode(n->a, x, y, w, ha, foc);
        tilenode(n->b, x, y + ha, w, h - ha, foc);
    }
}

static int draw_tag_box(Window win, int x, int y, const char *text,
    unsigned long bg, unsigned long fg, int minw)
{
    int pad = bartextpad;
    int w = textw(text) + pad * 2;
    if (w < minw) w = minw;
    XSetForeground(dpy, bargc, bg);
    XFillRectangle(dpy, win, bargc, x, y, w, barh);
    XSetForeground(dpy, bargc, fg);
    XDrawString(dpy, win, bargc, x + pad, y + barh - 8, text, (int)strlen(text));
    return w;
}

typedef enum {
    BAR_ITEM_NONE = 0,
    BAR_ITEM_WORKSPACES,
    BAR_ITEM_COMMAND,
    BAR_ITEM_TITLE,
    BAR_ITEM_CLOCK,
    BAR_ITEM_BATTERY,
    BAR_ITEM_MODE
} BarItem;

static BarItem parse_bar_item(const char *name) {
    if (!strcasecmp(name, "workspaces")) return BAR_ITEM_WORKSPACES;
    if (!strcasecmp(name, "command")) return BAR_ITEM_COMMAND;
    if (!strcasecmp(name, "title")) return BAR_ITEM_TITLE;
    if (!strcasecmp(name, "clock")) return BAR_ITEM_CLOCK;
    if (!strcasecmp(name, "battery")) return BAR_ITEM_BATTERY;
    if (!strcasecmp(name, "mode")) return BAR_ITEM_MODE;
    return BAR_ITEM_NONE;
}

static void build_bar_item_text(BarItem item, char *dst, size_t dstsz) {
    dst[0] = 0;
    switch (item) {
    case BAR_ITEM_COMMAND:
    case BAR_ITEM_MODE:
        build_mode_text(dst, dstsz);
        break;
    case BAR_ITEM_TITLE:
        build_title_text(dst, dstsz);
        break;
    case BAR_ITEM_CLOCK:
        build_clock_text(dst, dstsz);
        break;
    case BAR_ITEM_BATTERY:
        build_battery_text(dst, dstsz);
        break;
    default:
        break;
    }
}

static int workspace_section_width(void) {
    int width = 0;
    for (int i = 0; i < MAXWS; i++) {
        char part[8];
        if (!workspace_has_windows(i) && i != curws) continue;
        snprintf(part, sizeof part, "%d", i + 1);
        width += textw(part) + bartextpad * 2 + baritemgap;
    }
    return width;
}

static int draw_workspace_section(Window win, int x, int y) {
    int curx = x;
    for (int i = 0; i < MAXWS; i++) {
        char part[8];
        unsigned long bg = barbg, fg = barmutedfg;
        if (!workspace_has_windows(i) && i != curws) continue;
        snprintf(part, sizeof part, "%d", i + 1);
        if (i == curws) {
            bg = cnorm;
            fg = barfg;
        } else if (workspace_has_windows(i)) {
            fg = barfg;
        }
        curx += draw_tag_box(win, curx, y, part, bg, fg, barwsminw);
        curx += baritemgap;
    }
    return curx;
}

static int bar_item_width(BarItem item) {
    char tmp[256];

    if (item == BAR_ITEM_WORKSPACES) return workspace_section_width();
    build_bar_item_text(item, tmp, sizeof tmp);
    if (!tmp[0]) return 0;

    switch (item) {
    case BAR_ITEM_COMMAND:
        return textw(tmp) + bartextpad * 2 +
            ((mode == MODE_COMMAND && cmdline_len > 0) ? baritemgap + textw(cmdline) + bartextpad * 2 : 0);
    case BAR_ITEM_TITLE:
    case BAR_ITEM_CLOCK:
    case BAR_ITEM_BATTERY:
    case BAR_ITEM_MODE:
        return textw(tmp) + bartextpad * 2;
    default:
        return 0;
    }
}

static int draw_bar_item(Window win, int x, int y, BarItem item) {
    char tmp[256];
    int curx = x;

    if (item == BAR_ITEM_WORKSPACES) return draw_workspace_section(win, x, y);

    build_bar_item_text(item, tmp, sizeof tmp);
    if (!tmp[0]) return curx;

    switch (item) {
    case BAR_ITEM_COMMAND:
        curx += draw_tag_box(win, curx, y, tmp, baraccentbg, baraccentfg, 0);
        if (mode == MODE_COMMAND && cmdline_len > 0) {
            curx += baritemgap;
            curx += draw_tag_box(win, curx, y, cmdline, cnorm, barfg, 0);
        }
        return curx;
    case BAR_ITEM_TITLE:
        return curx + draw_tag_box(win, curx, y, tmp, barbg, barfg, 0);
    case BAR_ITEM_CLOCK:
    case BAR_ITEM_MODE:
        return curx + draw_tag_box(win, curx, y, tmp, baraccentbg, baraccentfg, 0);
    case BAR_ITEM_BATTERY:
        return curx + draw_tag_box(win, curx, y, tmp, cnorm, barfg, 0);
    default:
        return curx;
    }
}

static int section_width(const char *cfg) {
    char buf[128], *tok, *save;
    int width = 0;
    copystr(buf, sizeof buf, cfg);
    for (tok = strtok_r(buf, ",", &save); tok; tok = strtok_r(NULL, ",", &save)) {
        char item[128];
        BarItem kind;
        copystr(item, sizeof item, ltrim(tok));
        rtrim(item);
        kind = parse_bar_item(item);
        if (kind != BAR_ITEM_NONE) width += bar_item_width(kind) + baritemgap;
    }
    return width > 0 ? width - baritemgap : 0;
}

static int draw_section(Window win, int x, int y, const char *cfg) {
    char buf[128], *tok, *save;
    int curx = x;
    copystr(buf, sizeof buf, cfg);
    for (tok = strtok_r(buf, ",", &save); tok; tok = strtok_r(NULL, ",", &save)) {
        char item[128];
        BarItem kind;
        copystr(item, sizeof item, ltrim(tok));
        rtrim(item);
        kind = parse_bar_item(item);
        if (kind == BAR_ITEM_NONE) continue;
        curx = draw_bar_item(win, curx, y, kind);
        curx += baritemgap;
    }
    return curx;
}

static void drawbar(int mi) {
    if (!mons[mi].barwin) return;
    int leftx = barpadx, centx, rightx, leftw;
    int centerw = section_width(barcentercfg);
    int rightw = section_width(barrightcfg);

    XSetForeground(dpy, bargc, barbg);
    XFillRectangle(dpy, mons[mi].barwin, bargc, 0, 0, mons[mi].w, barh);

    leftw = section_width(barleftcfg);
    draw_section(mons[mi].barwin, leftx, 0, barleftcfg);
    rightx = mons[mi].w - rightw - barpadx;
    if (rightw > 0) draw_section(mons[mi].barwin, rightx, 0, barrightcfg);
    centx = (mons[mi].w - centerw) / 2;
    if (centerw > 0 && centx > leftx + leftw + 12 && centx + centerw < rightx - 12)
        draw_section(mons[mi].barwin, centx, 0, barcentercfg);
}

static int bar_uses_item(const char *item) {
    return strstr(barleftcfg, item) || strstr(barcentercfg, item) || strstr(barrightcfg, item);
}

static void drawbars_if_clock_changed(void) {
    time_t now = time(NULL);
    struct tm tm_now;
    if (!bar_uses_item("clock") && !bar_uses_item("battery")) return;
    localtime_r(&now, &tm_now);
    if (tm_now.tm_sec != last_clock_second) {
        drawbars();
    }
}

static void drawbars(void) {
    for (int i = 0; i < nmons; i++) drawbar(i);
    XFlush(dpy);
}

static void retile(void) {
    for (int i = 0; i < nmons; i++) {
        Mon *m = &mons[i];
        Node *fs = find_fullscreen_leaf(mon_tree(i));
        if (fs) {
            show_only_leaf(mon_tree(i), fs);
            drawborder(fs, fs == mon_focused(i));
            if (fs->real_fullscreen) {
                if (m->barwin) XUnmapWindow(dpy, m->barwin);
                XMoveResizeWindow(dpy, fs->win, m->x, m->y, m->w, m->h);
            } else {
                if (m->barwin) XMapRaised(dpy, m->barwin);
                XMoveResizeWindow(dpy, fs->win, m->wx, m->wy, m->ww - 2 * bw, m->wh - 2 * bw);
            }
            XRaiseWindow(dpy, fs->win);
        } else {
            if (m->barwin) XMapRaised(dpy, m->barwin);
            showtree(mon_tree(i));
            tilenode(mon_tree(i), m->wx, m->wy, m->ww, m->wh, mon_focused(i));
            raise_floating(mon_tree(i));
        }
        raise_bar_if_needed(i);
    }
    drawbars();
}

static void warpfocus(Node *n) {
    if (!n || !n->leaf) return;
    XWarpPointer(dpy, None, root, 0, 0, 0, 0, n->x + n->w / 2, n->y + n->h / 2);
}

static void setfocus(int mi, Node *n, int warp) {
    if (!n || !n->leaf) return;
    Node *prev = mon_focused(mi);
    mon_setfocused(mi, n);
    curmon = mi;
    if (prev && prev != n) drawborder(prev, 0);
    if (mode == MODE_INSERT) XSetInputFocus(dpy, n->win, RevertToPointerRoot, CurrentTime);
    XRaiseWindow(dpy, n->win);
    drawborder(n, 1);
    raise_floating(mon_tree(mi));
    raise_bar_if_needed(mi);
    if (warp) warpfocus(n);
    update_active_window();
}

static void showtree(Node *n) {
    if (!n) return;
    if (n->leaf) {
        XMapWindow(dpy, n->win);
        return;
    }
    showtree(n->a);
    showtree(n->b);
}

static void initatoms(void) {
    atom_net_active_window = XInternAtom(dpy, "_NET_ACTIVE_WINDOW", False);
    atom_net_client_list = XInternAtom(dpy, "_NET_CLIENT_LIST", False);
    atom_net_current_desktop = XInternAtom(dpy, "_NET_CURRENT_DESKTOP", False);
    atom_net_number_of_desktops = XInternAtom(dpy, "_NET_NUMBER_OF_DESKTOPS", False);
    atom_net_supported = XInternAtom(dpy, "_NET_SUPPORTED", False);
    atom_net_supporting_wm_check = XInternAtom(dpy, "_NET_SUPPORTING_WM_CHECK", False);
    atom_utf8_string = XInternAtom(dpy, "UTF8_STRING", False);
    atom_net_wm_window_type = XInternAtom(dpy, "_NET_WM_WINDOW_TYPE", False);
    atom_net_wm_window_type_dock = XInternAtom(dpy, "_NET_WM_WINDOW_TYPE_DOCK", False);
    atom_net_wm_window_type_dialog = XInternAtom(dpy, "_NET_WM_WINDOW_TYPE_DIALOG", False);
    atom_net_wm_window_type_utility = XInternAtom(dpy, "_NET_WM_WINDOW_TYPE_UTILITY", False);
    atom_net_wm_window_type_toolbar = XInternAtom(dpy, "_NET_WM_WINDOW_TYPE_TOOLBAR", False);
    atom_net_wm_window_type_splash = XInternAtom(dpy, "_NET_WM_WINDOW_TYPE_SPLASH", False);
    atom_net_wm_desktop = XInternAtom(dpy, "_NET_WM_DESKTOP", False);
    atom_net_wm_state = XInternAtom(dpy, "_NET_WM_STATE", False);
    atom_net_wm_state_fullscreen = XInternAtom(dpy, "_NET_WM_STATE_FULLSCREEN", False);
}

static void setup_wm_check(void) {
    static const char name[] = "nvwm";
    wmcheckwin = XCreateSimpleWindow(dpy, root, -1, -1, 1, 1, 0, 0, 0);
    XChangeProperty(dpy, wmcheckwin, atom_net_supporting_wm_check, XA_WINDOW, 32,
        PropModeReplace, (unsigned char *)&wmcheckwin, 1);
    XChangeProperty(dpy, root, atom_net_supporting_wm_check, XA_WINDOW, 32,
        PropModeReplace, (unsigned char *)&wmcheckwin, 1);
    XChangeProperty(dpy, wmcheckwin, XInternAtom(dpy, "_NET_WM_NAME", False),
        atom_utf8_string, 8, PropModeReplace, (const unsigned char *)name, (int)strlen(name));
}

static void update_supported_atoms(void) {
    Atom supported[] = {
        atom_net_active_window,
        atom_net_client_list,
        atom_net_current_desktop,
        atom_net_number_of_desktops,
        atom_net_wm_window_type,
        atom_net_wm_window_type_dock,
        atom_net_wm_window_type_dialog,
        atom_net_wm_window_type_utility,
        atom_net_wm_window_type_toolbar,
        atom_net_wm_window_type_splash,
        atom_net_wm_desktop,
        atom_net_wm_state,
        atom_net_wm_state_fullscreen,
    };
    XChangeProperty(dpy, root, atom_net_supported, XA_ATOM, 32, PropModeReplace,
        (unsigned char *)supported, (int)(sizeof supported / sizeof supported[0]));
}

static void collect_client_windows(Node *n, Window *list, int *count, int maxcount) {
    if (!n || *count >= maxcount) return;
    if (n->leaf) {
        list[(*count)++] = n->win;
        return;
    }
    collect_client_windows(n->a, list, count, maxcount);
    collect_client_windows(n->b, list, count, maxcount);
}

static void update_client_list(void) {
    Window list[1024];
    int count = 0;
    for (int mi = 0; mi < nmons; mi++) {
        for (int ws = 0; ws < MAXWS; ws++) {
            collect_client_windows(mon_tree_at(mi, ws), list, &count, 1024);
        }
    }
    XChangeProperty(dpy, root, atom_net_client_list, XA_WINDOW, 32, PropModeReplace,
        (unsigned char *)list, count);
}

static void update_current_desktop(void) {
    unsigned long ws = (unsigned long)curws;
    XChangeProperty(dpy, root, atom_net_current_desktop, XA_CARDINAL, 32, PropModeReplace,
        (unsigned char *)&ws, 1);
}

static void update_number_of_desktops(void) {
    unsigned long n = MAXWS;
    XChangeProperty(dpy, root, atom_net_number_of_desktops, XA_CARDINAL, 32, PropModeReplace,
        (unsigned char *)&n, 1);
}

static void update_active_window(void) {
    Window win = None;
    if (mon_focused(curmon)) win = mon_focused(curmon)->win;
    XChangeProperty(dpy, root, atom_net_active_window, XA_WINDOW, 32, PropModeReplace,
        (unsigned char *)&win, 1);
}

static void set_window_desktop(Window win, int ws) {
    unsigned long val = (unsigned long)ws;
    XChangeProperty(dpy, win, atom_net_wm_desktop, XA_CARDINAL, 32, PropModeReplace,
        (unsigned char *)&val, 1);
}

static void apply_rules(Node *n, int *targetws) {
    char class_name[64], instance_name[64], title[128];
    if (!n || !n->leaf) return;
    get_window_class(n->win, class_name, sizeof class_name, instance_name, sizeof instance_name);
    get_window_title(n->win, title, sizeof title);

    if (window_is_dialog_like(n->win)) n->floating = 1;

    for (int i = 0; i < nrules; i++) {
        Rule *r = &rules[i];
        int match = 1;
        if (r->class_name[0] && strcmp(r->class_name, class_name)) match = 0;
        if (r->instance_name[0] && strcmp(r->instance_name, instance_name)) match = 0;
        if (r->title[0] && strcmp(r->title, title)) match = 0;
        if (!match) continue;
        if (r->set_floating) n->floating = r->floating;
        if (targetws && r->workspace >= 0) *targetws = r->workspace;
    }
}

static void hidetree(Node *n) {
    if (!n) return;
    if (n->leaf) {
        unmap_managed(n);
        return;
    }
    hidetree(n->a);
    hidetree(n->b);
}

static void switch_workspace(int ws) {
    if (ws < 0 || ws >= MAXWS || ws == curws) return;
    for (int i = 0; i < nmons; i++) hidetree(mons[i].tree[curws]);
    curws = ws;
    for (int i = 0; i < nmons; i++) showtree(mons[i].tree[curws]);
    retile();
    update_current_desktop();
    if (mon_focused(curmon)) setfocus(curmon, mon_focused(curmon), 1);
    else update_active_window();
}

static void attach_to_ws(int mi, int ws, Node *leaf) {
    leaf->par = NULL;
    set_window_desktop(leaf->win, ws);
    if (!mon_tree_at(mi, ws)) {
        mon_settree_at(mi, ws, leaf);
        mon_setfocused_at(mi, ws, leaf);
        update_client_list();
        return;
    }
    Node *focused = mon_focused_at(mi, ws);
    Node *tree = mon_tree_at(mi, ws);
    Node *t = focused && focused->leaf ? focused : firstleaf(tree);
    int horiz = t->w > 0 ? (t->w >= t->h) : (mons[mi].ww >= mons[mi].wh);
    Node *sp = calloc(1, sizeof *sp);
    sp->ratio = 0.5f;
    sp->horiz = horiz;
    sp->par = t->par;
    sp->a = t;
    sp->b = leaf;
    if (!t->par) mon_settree_at(mi, ws, sp);
    else if (t->par->a == t) t->par->a = sp;
    else t->par->b = sp;
    t->par = sp;
    leaf->par = sp;
    mon_setfocused_at(mi, ws, leaf);
    update_client_list();
}

static void attach(int mi, Node *leaf) { attach_to_ws(mi, curws, leaf); }

static void detach_from_ws(int mi, int ws, Node *n) {
    if (!n->par) {
        mon_settree_at(mi, ws, NULL);
        mon_setfocused_at(mi, ws, NULL);
        update_client_list();
        return;
    }
    Node *p = n->par, *sib = p->a == n ? p->b : p->a;
    sib->par = p->par;
    if (!p->par) mon_settree_at(mi, ws, sib);
    else if (p->par->a == p) p->par->a = sib;
    else p->par->b = sib;
    if (mon_focused_at(mi, ws) == n) mon_setfocused_at(mi, ws, firstleaf(sib));
    free(p);
    n->par = NULL;
    update_client_list();
}

static void detach(int mi, Node *n) { detach_from_ws(mi, curws, n); }

static void removewin(Window w) {
    int mi = monforwin(w);
    Node *n = findleaf(mon_tree(mi), w);
    if (!n) return;
    if (drag_node == n) {
        drag_node = NULL;
        drag_mode = 0;
    }
    detach(mi, n);
    free(n);
    update_active_window();
}

static void collect_leaves(Node *n, Node **list, int *count, int maxcount) {
    if (!n || *count >= maxcount) return;
    if (n->leaf) {
        list[(*count)++] = n;
        return;
    }
    collect_leaves(n->a, list, count, maxcount);
    collect_leaves(n->b, list, count, maxcount);
}

static int interval_overlap(int a1, int a2, int b1, int b2) {
    int lo = a1 > b1 ? a1 : b1;
    int hi = a2 < b2 ? a2 : b2;
    return hi > lo ? hi - lo : 0;
}

static Node *find_directional_focus(int mi, Node *from, const char *dir) {
    Node *nodes[256];
    int count = 0;
    Node *best = NULL;
    long bestscore = 0;
    int fx1, fy1, fx2, fy2, fcx, fcy;

    if (!from) return NULL;
    collect_leaves(mon_tree(mi), nodes, &count, 256);
    fx1 = from->x;
    fy1 = from->y;
    fx2 = from->x + from->w;
    fy2 = from->y + from->h;
    fcx = from->x + from->w / 2;
    fcy = from->y + from->h / 2;

    for (int i = 0; i < count; i++) {
        Node *n = nodes[i];
        int nx1, ny1, nx2, ny2, ncx, ncy;
        int primary, secondary, overlap;
        long score;
        if (n == from) continue;
        nx1 = n->x;
        ny1 = n->y;
        nx2 = n->x + n->w;
        ny2 = n->y + n->h;
        ncx = n->x + n->w / 2;
        ncy = n->y + n->h / 2;

        if (!strcmp(dir, "left")) {
            primary = fx1 - nx2;
            overlap = interval_overlap(fy1, fy2, ny1, ny2);
            secondary = abs(fcy - ncy);
        } else if (!strcmp(dir, "right")) {
            primary = nx1 - fx2;
            overlap = interval_overlap(fy1, fy2, ny1, ny2);
            secondary = abs(fcy - ncy);
        } else if (!strcmp(dir, "up")) {
            primary = fy1 - ny2;
            overlap = interval_overlap(fx1, fx2, nx1, nx2);
            secondary = abs(fcx - ncx);
        } else {
            primary = ny1 - fy2;
            overlap = interval_overlap(fx1, fx2, nx1, nx2);
            secondary = abs(fcx - ncx);
        }

        if (primary <= 0) continue;
        score = (long)primary * 100000L + (long)(secondary - overlap) * 100L + secondary;
        if (!best || score < bestscore) {
            best = n;
            bestscore = score;
        }
    }
    if (!best) {
        if (!strcmp(dir, "left") || !strcmp(dir, "up")) return prevleaf(mi, from);
        return nextleaf(mi, from);
    }
    return best;
}

static int swap_in_direction(const char *dir) {
    Node *cur = mon_focused(curmon);
    Node *n;
    Window focused_win;
    if (!cur) return 1;
    n = find_directional_focus(curmon, cur, dir);
    if (!n || n == cur) return 1;
    focused_win = cur->win;
    swap_leaf_payload(cur, n);
    retile();
    setfocus(curmon, findleaf(mon_tree(curmon), focused_win), 1);
    return 1;
}

static void move_focused_to_workspace(int targetws) {
    Node *n;
    int srcmon = curmon;
    if (targetws < 0 || targetws >= MAXWS || targetws == curws) return;
    n = mon_focused(srcmon);
    if (!n) return;
    detach_from_ws(srcmon, curws, n);
    attach_to_ws(srcmon, targetws, n);
    hidetree(n);
    retile();
    if (mon_focused(curmon)) setfocus(curmon, mon_focused(curmon), 1);
}

static void move_focused_to_workspace_and_follow(int targetws) {
    if (targetws < 0 || targetws >= MAXWS || targetws == curws) return;
    move_focused_to_workspace(targetws);
    switch_workspace(targetws);
}

static void screenshot(void) {
    const char *cmd =
        "mkdir -p \"$HOME/Pictures/Screenshots\" && "
        "if command -v maim >/dev/null 2>&1; then "
        "maim \"$HOME/Pictures/Screenshots/$(date +%Y-%m-%d-%H%M%S).png\"; "
        "elif command -v scrot >/dev/null 2>&1; then "
        "scrot \"$HOME/Pictures/Screenshots/%Y-%m-%d-%H%M%S.png\"; "
        "elif command -v import >/dev/null 2>&1; then "
        "import -window root \"$HOME/Pictures/Screenshots/$(date +%Y-%m-%d-%H%M%S).png\"; "
        "fi";
    spawn(cmd);
}

static void spawn(const char *cmd) {
    if (fork() == 0) {
        setsid();
        execlp("sh", "sh", "-c", cmd, NULL);
        _exit(0);
    }
}

static void start_command_prompt(char prefix) {
    cmdline[0] = prefix;
    cmdline[1] = 0;
    cmdline_len = 1;
    enter_mode(MODE_COMMAND);
}

static void shell_quote_single(char *dst, size_t dstsz, const char *src) {
    size_t pos = 0;
    if (!dstsz) return;
    dst[0] = 0;
    if (pos + 1 < dstsz) dst[pos++] = '\'';
    for (; *src && pos + 1 < dstsz; src++) {
        if (*src == '\'') {
            static const char repl[] = "'\\''";
            for (size_t i = 0; repl[i] && pos + 1 < dstsz; i++) dst[pos++] = repl[i];
        } else {
            dst[pos++] = *src;
        }
    }
    if (pos + 1 < dstsz) dst[pos++] = '\'';
    dst[pos] = 0;
}

static void spawn_in_terminal(const char *cmd) {
    char quoted[CMDLINE_MAX * 4];
    char full[CMDLINE_MAX * 4 + 256];

    if (!cmd || !*cmd) {
        spawn(term);
        return;
    }

    shell_quote_single(quoted, sizeof quoted, cmd);
    snprintf(full, sizeof full, "%s -e sh -lc %s", term, quoted);
    spawn(full);
}

static int parse_mods(const char *keys) {
    int mask = 0;
    if (strstr(keys, "mod")) mask |= Mod4Mask;
    if (strstr(keys, "shift")) mask |= ShiftMask;
    if (strstr(keys, "ctrl")) mask |= ControlMask;
    if (strstr(keys, "alt")) mask |= Mod1Mask;
    return mask;
}

static void reset_config_defaults(void) {
    gap = 8;
    bw = 2;
    barh = 24;
    barpadx = 10;
    baritemgap = 6;
    bartextpad = 8;
    barwsminw = 20;
    cfocus = 0x5588ff;
    cnorm = 0x333333;
    barbg = 0x111111;
    barfg = 0xeeeeee;
    baraccentbg = 0x5588ff;
    baraccentfg = 0x111111;
    barmutedfg = 0xaaaaaa;
    copystr(term, sizeof term, "st");
    copystr(barfontname, sizeof barfontname, "9x15");
    copystr(barleftcfg, sizeof barleftcfg, "command,title,workspaces");
    copystr(barcentercfg, sizeof barcentercfg, "command");
    copystr(barrightcfg, sizeof barrightcfg, "clock");
    barpos = BAR_TOP;
    nmodbinds = 0;
    nnormalbinds = 0;
    ncmdbinds = 0;
    nrules = 0;
    nautostart = 0;
    modbind_limit = MAXBINDS;
    normalbind_limit = MAXMODEBINDS;
    cmd_limit = MAXCMDS;
    autostart_limit = MAXAUTOSTART;
}

static void updatenumlockmask(void) {
    XModifierKeymap *modmap;
    numlockmask = 0;
    modmap = XGetModifierMapping(dpy);
    if (!modmap) return;
    for (int mod = 0; mod < 8; mod++) {
        for (int k = 0; k < modmap->max_keypermod; k++) {
            KeyCode code = modmap->modifiermap[mod * modmap->max_keypermod + k];
            if (!code) continue;
            if (XkbKeycodeToKeysym(dpy, code, 0, 0) == XK_Num_Lock) {
                numlockmask = (1u << mod);
            }
        }
    }
    XFreeModifiermap(modmap);
}

static void upsert_modbind(unsigned int mod, KeyCode code, const char *action) {
    for (int i = 0; i < nmodbinds; i++) {
        if (modbinds[i].mod == mod && modbinds[i].code == code) {
            copystr(modbinds[i].action, sizeof modbinds[i].action, action);
            return;
        }
    }
    if (nmodbinds >= modbind_limit) return;
    modbinds[nmodbinds].mod = mod;
    modbinds[nmodbinds].code = code;
    copystr(modbinds[nmodbinds].action, sizeof modbinds[nmodbinds].action, action);
    nmodbinds++;
}

static void upsert_normalbind(KeySym sym, const char *action) {
    for (int i = 0; i < nnormalbinds; i++) {
        if (normalbinds[i].sym == sym) {
            copystr(normalbinds[i].action, sizeof normalbinds[i].action, action);
            return;
        }
    }
    if (nnormalbinds >= normalbind_limit) return;
    normalbinds[nnormalbinds].sym = sym;
    copystr(normalbinds[nnormalbinds].action, sizeof normalbinds[nnormalbinds].action, action);
    nnormalbinds++;
}

static void upsert_cmdbind(const char *name, const char *action) {
    for (int i = 0; i < ncmdbinds; i++) {
        if (!strcmp(cmdbinds[i].name, name)) {
            copystr(cmdbinds[i].action, sizeof cmdbinds[i].action, action);
            return;
        }
    }
    if (ncmdbinds >= cmd_limit) return;
    copystr(cmdbinds[ncmdbinds].name, sizeof cmdbinds[ncmdbinds].name, name);
    copystr(cmdbinds[ncmdbinds].action, sizeof cmdbinds[ncmdbinds].action, action);
    ncmdbinds++;
}

static void add_autostart_cmd(const char *cmd) {
    if (!cmd || !*cmd || nautostart >= autostart_limit) return;
    copystr(autostart_cmds[nautostart], sizeof autostart_cmds[nautostart], cmd);
    nautostart++;
}

static int parse_bind_config(const char *line) {
    char mode_name[64], keyexpr[128], action[256];

    if (sscanf(line, "bind_%63[^ ] = %127[^=]= %255[^\n]", mode_name, keyexpr, action) != 3) return 0;
    rtrim(mode_name);
    rtrim(keyexpr);
    rtrim(action);
    if (!strcasecmp(mode_name, "insert")) {
        char *kp = strrchr(keyexpr, '+');
        KeySym sym;
        KeyCode code;

        kp = kp ? kp + 1 : keyexpr;
        kp = ltrim(kp);
        if (!*kp) return 1;
        sym = parse_keysym_name(kp);
        if (sym == NoSymbol) return 1;
        code = XKeysymToKeycode(dpy, sym);
        if (code) upsert_modbind(parse_mods(keyexpr), code, action);
        return 1;
    }
    if (!strcasecmp(mode_name, "normal")) {
        KeySym sym = parse_keysym_name(keyexpr);
        if (sym != NoSymbol) upsert_normalbind(sym, action);
        return 1;
    }
    return 1;
}

static int parse_command_config(const char *line) {
    char cmd_name[64], cmd_action[256];

    if (sscanf(line, "command = %63[^=]= %255[^\n]", cmd_name, cmd_action) != 2) return 0;
    rtrim(cmd_name);
    rtrim(cmd_action);
    upsert_cmdbind(skip_command_prefix(cmd_name), cmd_action);
    return 1;
}

static int parse_rule_config(const char *line) {
    char rule_match[128], rule_action[128];
    Rule *r;
    char *kind, *value;
    char *act;

    if (sscanf(line, "rule = %127[^=]= %127[^\n]", rule_match, rule_action) != 2) return 0;
    rtrim(rule_match);
    rtrim(rule_action);
    if (nrules >= MAXRULES) return 1;

    r = &rules[nrules];
    memset(r, 0, sizeof *r);
    r->workspace = -1;
    kind = ltrim(rule_match);
    value = strchr(kind, ':');
    if (!value) return 1;
    *value++ = 0;
    kind = ltrim(kind);
    value = ltrim(value);
    if (!strcasecmp(kind, "class")) copystr(r->class_name, sizeof r->class_name, value);
    else if (!strcasecmp(kind, "instance")) copystr(r->instance_name, sizeof r->instance_name, value);
    else if (!strcasecmp(kind, "title")) copystr(r->title, sizeof r->title, value);
    else return 1;

    for (act = strtok(rule_action, ","); act; act = strtok(NULL, ",")) {
        act = ltrim(act);
        rtrim(act);
        if (!strcasecmp(act, "float")) {
            r->set_floating = 1;
            r->floating = 1;
        } else if (!strcasecmp(act, "tile")) {
            r->set_floating = 1;
            r->floating = 0;
        } else if (!strncasecmp(act, "workspace:", 10)) {
            int ws = atoi(act + 10);
            if (ws >= 1 && ws <= MAXWS) r->workspace = ws - 1;
        }
    }
    nrules++;
    return 1;
}

static int parse_key_value(char *line, char *k, size_t ksz, char *v, size_t vsz) {
    char *eq = strchr(line, '=');
    if (!eq) return 0;
    *eq = 0;
    copystr(k, ksz, ltrim(line));
    rtrim(k);
    copystr(v, vsz, ltrim(eq + 1));
    rtrim(v);
    return 1;
}

static int apply_limit_config(const char *k, const char *v) {
    if (!strcmp(k, "insert_bind_limit")) modbind_limit = clampi(atoi(v), 1, MAXBINDS);
    else if (!strcmp(k, "normal_bind_limit")) normalbind_limit = clampi(atoi(v), 1, MAXMODEBINDS);
    else if (!strcmp(k, "command_limit")) cmd_limit = clampi(atoi(v), 1, MAXCMDS);
    else if (!strcmp(k, "autostart_limit")) autostart_limit = clampi(atoi(v), 1, MAXAUTOSTART);
    else return 0;
    return 1;
}

static int apply_scalar_config(const char *k, const char *v) {
    if (!strcmp(k, "gap")) gap = atoi(v);
    else if (!strcmp(k, "border")) bw = atoi(v);
    else if (!strcmp(k, "bar_height")) barh = atoi(v);
    else if (!strcmp(k, "bar_padding_x")) barpadx = atoi(v);
    else if (!strcmp(k, "bar_item_gap")) baritemgap = atoi(v);
    else if (!strcmp(k, "bar_text_padding")) bartextpad = atoi(v);
    else if (!strcmp(k, "bar_workspace_min_width")) barwsminw = atoi(v);
    else if (!strcmp(k, "border_focus")) cfocus = hcol(v);
    else if (!strcmp(k, "border_normal")) cnorm = hcol(v);
    else if (!strcmp(k, "bar_bg")) barbg = hcol(v);
    else if (!strcmp(k, "bar_fg")) barfg = hcol(v);
    else if (!strcmp(k, "bar_accent_bg")) baraccentbg = hcol(v);
    else if (!strcmp(k, "bar_accent_fg")) baraccentfg = hcol(v);
    else if (!strcmp(k, "bar_muted_fg")) barmutedfg = hcol(v);
    else if (!strcmp(k, "bar_font")) copystr(barfontname, sizeof barfontname, v);
    else if (!strcmp(k, "bar_left")) copystr(barleftcfg, sizeof barleftcfg, v);
    else if (!strcmp(k, "bar_center")) copystr(barcentercfg, sizeof barcentercfg, v);
    else if (!strcmp(k, "bar_right")) copystr(barrightcfg, sizeof barrightcfg, v);
    else if (!strcmp(k, "bar_position")) {
        if (!strcasecmp(v, "bottom")) barpos = BAR_BOTTOM;
        else barpos = BAR_TOP;
    } else if (!strcmp(k, "terminal")) {
        copystr(term, sizeof term, v);
    } else {
        return 0;
    }
    return 1;
}

static void grab_mod_binds(void) {
    for (int i = 0; i < nmodbinds; i++) {
        XGrabKey(dpy, modbinds[i].code, modbinds[i].mod, root, True, GrabModeAsync, GrabModeAsync);
        XGrabKey(dpy, modbinds[i].code, modbinds[i].mod | LockMask, root, True, GrabModeAsync, GrabModeAsync);
        if (numlockmask) {
            XGrabKey(dpy, modbinds[i].code, modbinds[i].mod | numlockmask, root, True, GrabModeAsync, GrabModeAsync);
            XGrabKey(dpy, modbinds[i].code, modbinds[i].mod | numlockmask | LockMask,
                root, True, GrabModeAsync, GrabModeAsync);
        }
    }
}

static void loadcfg_file(const char *path) {
    FILE *f = fopen(path, "r");
    if (!f) return;
    char line[512], k[64], v[448];
    while (fgets(line, sizeof line, f)) {
        char *p = ltrim(line);
        if (!*p || *p == '#') continue;
        if (parse_bind_config(p) || parse_command_config(p) || parse_rule_config(p)) continue;
        if (!parse_key_value(p, k, sizeof k, v, sizeof v)) continue;
        if (!strcmp(k, "autostart")) {
            add_autostart_cmd(v);
            continue;
        }
        if (apply_limit_config(k, v)) continue;
        apply_scalar_config(k, v);
    }
    fclose(f);
}

static void loadcfg(void) {
    char homecfg[PATH_MAX];
    const char *home = getenv("HOME");
    if (home && *home) {
        snprintf(homecfg, sizeof homecfg, "%s/.config/nvwm/config.conf", home);
    } else {
        homecfg[0] = 0;
    }

    reset_config_defaults();
    if (homecfg[0]) loadcfg_file(homecfg);
    else loadcfg_file("/etc/nvwm/config.conf");
}

static void run_autostart(void) {
    for (int i = 0; i < nautostart; i++) spawn(autostart_cmds[i]);
}

static void reloadwm(void) {
    XUngrabKey(dpy, AnyKey, AnyModifier, root);
    loadcfg();
    updatenumlockmask();
    grab_mod_binds();
    setupbars();
    retile();
    if (mon_focused(curmon)) setfocus(curmon, mon_focused(curmon), 0);
    else update_active_window();
    drawbars();
}

static void set_net_wm_state(Window win, int fullscreen) {
    if (fullscreen) {
        Atom atoms[1] = { atom_net_wm_state_fullscreen };
        XChangeProperty(dpy, win, atom_net_wm_state, XA_ATOM, 32, PropModeReplace, (unsigned char *)atoms, 1);
    } else {
        XDeleteProperty(dpy, win, atom_net_wm_state);
    }
}

static int window_wants_fullscreen(Window win) {
    Atom actual;
    int format;
    unsigned long nitems, bytes_after;
    unsigned char *data = NULL;
    int wants = 0;

    if (XGetWindowProperty(dpy, win, atom_net_wm_state, 0, 32, False, XA_ATOM, &actual,
            &format, &nitems, &bytes_after, &data) == Success && data) {
        Atom *atoms = (Atom *)data;
        for (unsigned long i = 0; i < nitems; i++) {
            if (atoms[i] == atom_net_wm_state_fullscreen) {
                wants = 1;
                break;
            }
        }
        XFree(data);
    }
    return wants;
}

static void apply_real_fullscreen(Node *n, Window win, int mi, int ws, int want, int focus_if_visible) {
    if (!n) return;
    if (n->real_fullscreen == want) return;
    n->real_fullscreen = want;
    if (want) {
        n->fullscreen = 0;
        n->floating = 0;
    }
    set_net_wm_state(win, want);
    retile();
    if (ws == curws) {
        mon_setfocused_at(mi, ws, n);
        if (focus_if_visible && mode == MODE_INSERT) setfocus(mi, n, 0);
        else XRaiseWindow(dpy, n->win);
    }
}

static void handle_client_fullscreen(Window win, long action, Atom a1, Atom a2) {
    int mi = 0, ws = 0;
    Node *n;
    int wants = 0;
    if (a1 != atom_net_wm_state_fullscreen && a2 != atom_net_wm_state_fullscreen) return;
    n = findleaf_any(win, &mi, &ws);
    if (!n) return;
    if (action == 1) wants = 1;
    else if (action == 0) wants = 0;
    else if (action == 2) wants = !n->real_fullscreen;
    else return;
    apply_real_fullscreen(n, win, mi, ws, wants, 1);
}

static void sync_window_fullscreen(Window win) {
    int mi = 0, ws = 0;
    Node *n = findleaf_any(win, &mi, &ws);
    if (!n) return;
    apply_real_fullscreen(n, n->win, mi, ws, window_wants_fullscreen(win), 0);
}

static void enter_mode(InputMode newmode) {
    if (newmode == MODE_INSERT) {
        mode = MODE_INSERT;
        cmdline[0] = 0;
        cmdline_len = 0;
        if (keyboard_grabbed) {
            XUngrabKeyboard(dpy, CurrentTime);
            keyboard_grabbed = 0;
        }
        if (mon_focused(curmon)) setfocus(curmon, mon_focused(curmon), 0);
    } else {
        if (!keyboard_grabbed) {
            if (XGrabKeyboard(dpy, root, True, GrabModeAsync, GrabModeAsync, CurrentTime) == GrabSuccess) {
                keyboard_grabbed = 1;
            }
        }
        mode = newmode;
        if (newmode == MODE_NORMAL) {
            cmdline[0] = 0;
            cmdline_len = 0;
        } else if (!cmdline_len) {
            copystr(cmdline, sizeof cmdline, ":");
            cmdline_len = 1;
        }
    }
    drawbars();
}

static int apply_wm_action(const char *action) {
    Mon *m = &mons[curmon];
    if (!strncmp(action, "spawn:", 6)) {
        spawn(action + 6);
        return 1;
    }
    if (!strncmp(action, "wm:mode:", 8)) {
        const char *name = action + 8;
        if (!strcmp(name, "insert")) enter_mode(MODE_INSERT);
        else if (!strcmp(name, "normal")) enter_mode(MODE_NORMAL);
        else if (!strcmp(name, "command")) {
            copystr(cmdline, sizeof cmdline, ":");
            cmdline_len = 1;
            enter_mode(MODE_COMMAND);
        }
        return 1;
    }
    if (!strcmp(action, "wm:quit")) {
        running = 0;
        return 1;
    }
    if (!strcmp(action, "wm:kill")) {
        if (mon_focused(curmon)) XKillClient(dpy, mon_focused(curmon)->win);
        return 1;
    }
    if (!strcmp(action, "wm:reload")) {
        reloadwm();
        return 1;
    }
    if (!strcmp(action, "wm:focus_next")) {
        Node *n = nextleaf(curmon, mon_focused(curmon));
        if (n && n != mon_focused(curmon)) setfocus(curmon, n, 1);
        return 1;
    }
    if (!strcmp(action, "wm:focus_prev")) {
        Node *n = prevleaf(curmon, mon_focused(curmon));
        if (n && n != mon_focused(curmon)) setfocus(curmon, n, 1);
        return 1;
    }
    if (!strcmp(action, "wm:swap_next")) {
        Node *cur = mon_focused(curmon);
        Node *n = nextleaf(curmon, cur);
        if (cur && n && n != cur) {
            Window focused_win = cur->win;
            swap_leaf_payload(cur, n);
            retile();
            setfocus(curmon, findleaf(mon_tree(curmon), focused_win), 1);
        }
        return 1;
    }
    if (!strcmp(action, "wm:swap_prev")) {
        Node *cur = mon_focused(curmon);
        Node *n = prevleaf(curmon, cur);
        if (cur && n && n != cur) {
            Window focused_win = cur->win;
            swap_leaf_payload(cur, n);
            retile();
            setfocus(curmon, findleaf(mon_tree(curmon), focused_win), 1);
        }
        return 1;
    }
    if (!strcmp(action, "wm:swap_left")) return swap_in_direction("left");
    if (!strcmp(action, "wm:swap_right")) return swap_in_direction("right");
    if (!strcmp(action, "wm:swap_up")) return swap_in_direction("up");
    if (!strcmp(action, "wm:swap_down")) return swap_in_direction("down");
    if (!strcmp(action, "wm:focus_left")) {
        Node *n = find_directional_focus(curmon, mon_focused(curmon), "left");
        if (n) setfocus(curmon, n, 1);
        return 1;
    }
    if (!strcmp(action, "wm:focus_right")) {
        Node *n = find_directional_focus(curmon, mon_focused(curmon), "right");
        if (n) setfocus(curmon, n, 1);
        return 1;
    }
    if (!strcmp(action, "wm:focus_up")) {
        Node *n = find_directional_focus(curmon, mon_focused(curmon), "up");
        if (n) setfocus(curmon, n, 1);
        return 1;
    }
    if (!strcmp(action, "wm:focus_down")) {
        Node *n = find_directional_focus(curmon, mon_focused(curmon), "down");
        if (n) setfocus(curmon, n, 1);
        return 1;
    }
    if (!strncmp(action, "wm:workspace:", 13)) {
        switch_workspace(atoi(action + 13) - 1);
        return 1;
    }
    if (!strcmp(action, "wm:workspace_prev")) {
        switch_workspace((curws + MAXWS - 1) % MAXWS);
        return 1;
    }
    if (!strcmp(action, "wm:workspace_next")) {
        switch_workspace((curws + 1) % MAXWS);
        return 1;
    }
    if (!strncmp(action, "wm:move_to_workspace:", 21)) {
        move_focused_to_workspace(atoi(action + 21) - 1);
        return 1;
    }
    if (!strcmp(action, "wm:move_to_workspace_prev")) {
        move_focused_to_workspace_and_follow((curws + MAXWS - 1) % MAXWS);
        return 1;
    }
    if (!strcmp(action, "wm:move_to_workspace_next")) {
        move_focused_to_workspace_and_follow((curws + 1) % MAXWS);
        return 1;
    }
    if (!strcmp(action, "wm:toggle_float")) {
        if (!mon_focused(curmon)) return 1;
        mon_focused(curmon)->floating ^= 1;
        if (mon_focused(curmon)->floating) {
            int fw = m->ww / 2;
            int fh = m->wh / 2;
            int fx = m->wx + (m->ww - fw) / 2;
            int fy = m->wy + (m->wh - fh) / 2;
            XMoveResizeWindow(dpy, mon_focused(curmon)->win, fx, fy, fw - 2 * bw, fh - 2 * bw);
            XRaiseWindow(dpy, mon_focused(curmon)->win);
        }
        retile();
        return 1;
    }
    if (!strcmp(action, "wm:toggle_fullscreen")) {
        if (!mon_focused(curmon)) return 1;
        mon_focused(curmon)->fullscreen ^= 1;
        if (mon_focused(curmon)->fullscreen) {
            mon_focused(curmon)->floating = 0;
            mon_focused(curmon)->real_fullscreen = 0;
        }
        retile();
        XRaiseWindow(dpy, mon_focused(curmon)->win);
        return 1;
    }
    if (!strcmp(action, "wm:screenshot")) {
        screenshot();
        return 1;
    }
    if (!strcmp(action, "wm:toggle_split")) {
        if (mon_focused(curmon) && mon_focused(curmon)->par) {
            mon_focused(curmon)->par->horiz ^= 1;
            retile();
        }
        return 1;
    }
    if (!strncmp(action, "wm:ratio:", 9)) {
        if (mon_focused(curmon) && mon_focused(curmon)->par) {
            float delta = strtof(action + 9, NULL);
            mon_focused(curmon)->par->ratio += delta;
            if (mon_focused(curmon)->par->ratio < 0.1f) mon_focused(curmon)->par->ratio = 0.1f;
            if (mon_focused(curmon)->par->ratio > 0.9f) mon_focused(curmon)->par->ratio = 0.9f;
            retile();
        }
        return 1;
    }
    return 0;
}

static int run_command_line(void) {
    if (cmdline_len < 2 || (cmdline[0] != ':' && cmdline[0] != '/')) {
        enter_mode(MODE_NORMAL);
        return 0;
    }

    if (cmdline[0] == '/') {
        const char *cmd = cmdline + 1;
        if (*cmd) spawn(cmd);
        enter_mode(MODE_NORMAL);
        return 1;
    }

    {
        const char *name = cmdline + 1;
        if (!strncmp(name, "t ", 2)) {
            while (*name == 't' || *name == ' ') name++;
            spawn_in_terminal(name);
            enter_mode(MODE_NORMAL);
            return 1;
        }
        if (!strcmp(name, "t")) {
            spawn_in_terminal("");
            enter_mode(MODE_NORMAL);
            return 1;
        }
        for (int i = 0; i < ncmdbinds; i++) {
            if (!strcmp(name, cmdbinds[i].name)) {
                int keep = apply_wm_action(cmdbinds[i].action);
                if (mode == MODE_COMMAND) enter_mode(MODE_NORMAL);
                return keep;
            }
        }
        if (!strcmp(name, "w!")) {
            int keep = apply_wm_action("wm:reload");
            if (mode == MODE_COMMAND) enter_mode(MODE_NORMAL);
            return keep;
        }
        if (!strcmp(name, "q!")) {
            int keep = apply_wm_action("wm:quit");
            if (mode == MODE_COMMAND) enter_mode(MODE_NORMAL);
            return keep;
        }
    }
    enter_mode(MODE_NORMAL);
    return 0;
}

static void handle_command_key(XKeyEvent *kev, KeySym sym) {
    char text[32];
    int len = XLookupString(kev, text, sizeof text, NULL, NULL);

    if (sym == XK_Return || sym == XK_KP_Enter) {
        run_command_line();
        return;
    }
    if (sym == XK_Escape) {
        enter_mode(MODE_NORMAL);
        return;
    }
    if (sym == XK_BackSpace) {
        if (cmdline_len > 1) cmdline[--cmdline_len] = 0;
        drawbars();
        return;
    }
    if (len <= 0) return;
    for (int i = 0; i < len; i++) {
        if (cmdline_len < CMDLINE_MAX - 1 && text[i] >= 32 && text[i] < 127) {
            cmdline[cmdline_len++] = text[i];
            cmdline[cmdline_len] = 0;
        }
    }
    drawbars();
}

static int handle_normal_key(XKeyEvent *kev, KeySym sym) {
    char text[32];
    int len = XLookupString(kev, text, sizeof text, NULL, NULL);

    if (len > 0 && text[0] == ':') {
        start_command_prompt(':');
        return 1;
    }
    if (len > 0 && text[0] == '/') {
        start_command_prompt('/');
        return 1;
    }
    if (sym == XK_Escape) {
        enter_mode(MODE_INSERT);
        return 1;
    }
    if (sym == XK_Left || sym == XK_KP_Left) return apply_wm_action("wm:focus_prev");
    if (sym == XK_Right || sym == XK_KP_Right) return apply_wm_action("wm:focus_next");
    if (sym == XK_Up || sym == XK_KP_Up) return apply_wm_action("wm:focus_up");
    if (sym == XK_Down || sym == XK_KP_Down) return apply_wm_action("wm:focus_down");
    for (int i = 0; i < nnormalbinds; i++) {
        if (normalbinds[i].sym == sym) {
            return apply_wm_action(normalbinds[i].action);
        }
    }
    return 0;
}

static void setupbars(void) {
    XGCValues gcv;
    XClassHint hint;
    Atom dock_type[1] = { atom_net_wm_window_type_dock };
    if (bargc) XFreeGC(dpy, bargc);
    if (barfont) {
        XFreeFont(dpy, barfont);
        barfont = NULL;
    }
    barfont = XLoadQueryFont(dpy, barfontname);
    if (!barfont) barfont = XLoadQueryFont(dpy, "9x15");
    if (!barfont) barfont = XLoadQueryFont(dpy, "fixed");
    bargc = XCreateGC(dpy, root, 0, &gcv);
    if (barfont) XSetFont(dpy, bargc, barfont->fid);

    for (int i = 0; i < nmons; i++) {
        Mon *m = &mons[i];
        m->wx = m->x;
        m->ww = m->w;
        m->wh = m->h - barh;
        if (m->wh < 1) m->wh = 1;
        if (barpos == BAR_TOP) {
            m->wy = m->y + barh;
            if (!m->barwin) m->barwin = XCreateSimpleWindow(dpy, root, m->x, m->y, m->w, barh, 0, barbg, barbg);
            XMoveResizeWindow(dpy, m->barwin, m->x, m->y, m->w, barh);
        } else {
            m->wy = m->y;
            if (!m->barwin) m->barwin = XCreateSimpleWindow(dpy, root, m->x, m->y + m->h - barh, m->w, barh, 0, barbg, barbg);
            XMoveResizeWindow(dpy, m->barwin, m->x, m->y + m->h - barh, m->w, barh);
        }
        XSetWindowBackground(dpy, m->barwin, barbg);
        XClearWindow(dpy, m->barwin);
        XChangeProperty(dpy, m->barwin, atom_net_wm_window_type, XA_ATOM, 32,
            PropModeReplace, (unsigned char *)dock_type, 1);
        XStoreName(dpy, m->barwin, "nvwm-bar");
        hint.res_name = "nvwm-bar";
        hint.res_class = "NVWMBar";
        XSetClassHint(dpy, m->barwin, &hint);
        XDefineCursor(dpy, m->barwin, normalcursor);
        XSelectInput(dpy, m->barwin, ExposureMask);
        XMapRaised(dpy, m->barwin);
    }
    drawbars();
}

int main(void) {
    signal(SIGCHLD, SIG_IGN);
    dpy = XOpenDisplay(NULL);
    if (!dpy) return 1;
    XSetErrorHandler(xerr);

    int scr = DefaultScreen(dpy);
    root = RootWindow(dpy, scr);
    sw = DisplayWidth(dpy, scr);
    sh = DisplayHeight(dpy, scr);
    normalcursor = XCreateFontCursor(dpy, XC_left_ptr);
    movecursor = XCreateFontCursor(dpy, XC_fleur);
    resizecursor = XCreateFontCursor(dpy, XC_bottom_right_corner);
    XDefineCursor(dpy, root, normalcursor);
    initatoms();
    setup_wm_check();
    update_supported_atoms();
    update_number_of_desktops();
    update_current_desktop();
    update_active_window();

    int xiev, xierr;
    if (XineramaQueryExtension(dpy, &xiev, &xierr) && XineramaIsActive(dpy)) {
        int n;
        XineramaScreenInfo *xi = XineramaQueryScreens(dpy, &n);
        nmons = n < MAXMONS ? n : MAXMONS;
        for (int i = 0; i < nmons; i++) {
            mons[i].x = xi[i].x_org;
            mons[i].y = xi[i].y_org;
            mons[i].w = xi[i].width;
            mons[i].h = xi[i].height;
        }
        XFree(xi);
    } else {
        nmons = 1;
        mons[0].x = 0;
        mons[0].y = 0;
        mons[0].w = sw;
        mons[0].h = sh;
    }

    XSelectInput(dpy, root, SubstructureNotifyMask | SubstructureRedirectMask | KeyPressMask);

    loadcfg();
    updatenumlockmask();
    grab_mod_binds();
    setupbars();
    run_autostart();

    XGrabButton(dpy, Button1, MOD, root, False,
        ButtonPressMask | ButtonReleaseMask,
        GrabModeAsync, GrabModeAsync, None, None);
    XGrabButton(dpy, Button3, MOD, root, False,
        ButtonPressMask | ButtonReleaseMask,
        GrabModeAsync, GrabModeAsync, None, None);

    while (running) {
        while (XPending(dpy)) {
            XEvent ev;
            XNextEvent(dpy, &ev);
            switch (ev.type) {
        case Expose:
            for (int i = 0; i < nmons; i++) {
                if (ev.xexpose.window == mons[i].barwin) {
                    drawbar(i);
                    break;
                }
            }
            break;

        case MapRequest:
            XSelectInput(dpy, ev.xmaprequest.window, EnterWindowMask | PropertyChangeMask);
            XMapWindow(dpy, ev.xmaprequest.window);
            {
                Window dw;
                int rx, ry, wx, wy;
                unsigned msk;
                Node *n;
                int targetws = curws;
                XQueryPointer(dpy, root, &dw, &dw, &rx, &ry, &wx, &wy, &msk);
                int mi = monforpt(rx, ry);
                n = mkleaf(ev.xmaprequest.window);
                apply_rules(n, &targetws);
                if (window_has_atom(ev.xmaprequest.window, atom_net_wm_state,
                        atom_net_wm_state_fullscreen)) {
                    n->real_fullscreen = 1;
                }
                attach_to_ws(mi, targetws, n);
                if (targetws != curws) unmap_managed(n);
                retile();
                if (targetws == curws) setfocus(mi, n, 1);
            }
            break;

        case DestroyNotify:
            removewin(ev.xdestroywindow.window);
            retile();
            if (mon_focused(curmon)) setfocus(curmon, mon_focused(curmon), 0);
            break;

        case UnmapNotify:
            {
                int mi = 0, ws = 0;
                Node *n = findleaf_any(ev.xunmap.window, &mi, &ws);
                if (n) {
                    if (n->ignore_unmap > 0) {
                        n->ignore_unmap--;
                    } else {
                        removewin(ev.xunmap.window);
                        retile();
                        if (mon_focused(curmon)) setfocus(curmon, mon_focused(curmon), 0);
                    }
                } else if (ev.xunmap.send_event) {
                    removewin(ev.xunmap.window);
                    retile();
                    if (mon_focused(curmon)) setfocus(curmon, mon_focused(curmon), 0);
                }
            }
            break;

        case PropertyNotify:
            if (ev.xproperty.atom == atom_net_wm_state) {
                sync_window_fullscreen(ev.xproperty.window);
            }
            break;

        case ClientMessage:
            if (ev.xclient.message_type == atom_net_current_desktop) {
                switch_workspace((int)ev.xclient.data.l[0]);
                break;
            }
            if (ev.xclient.message_type == atom_net_active_window) {
                int mi = monforwin(ev.xclient.window);
                Node *n = findleaf(mon_tree(mi), ev.xclient.window);
                if (n) setfocus(mi, n, 0);
                break;
            }
            if (ev.xclient.message_type == atom_net_wm_state) {
                handle_client_fullscreen(ev.xclient.window, ev.xclient.data.l[0],
                    (Atom)ev.xclient.data.l[1], (Atom)ev.xclient.data.l[2]);
                break;
            }
            break;

        case ConfigureRequest: {
            XWindowChanges wc = {
                .x = ev.xconfigurerequest.x,
                .y = ev.xconfigurerequest.y,
                .width = ev.xconfigurerequest.width,
                .height = ev.xconfigurerequest.height,
                .border_width = bw,
                .sibling = ev.xconfigurerequest.above,
                .stack_mode = ev.xconfigurerequest.detail,
            };
            XConfigureWindow(dpy, ev.xconfigurerequest.window,
                ev.xconfigurerequest.value_mask, &wc);
            break;
        }

        case EnterNotify:
            if (mode != MODE_INSERT) break;
            if (ev.xcrossing.mode == NotifyNormal) {
                int mi = monforwin(ev.xcrossing.window);
                Node *n = findleaf(mon_tree(mi), ev.xcrossing.window);
                if (n && n != mon_focused(mi)) setfocus(mi, n, 0);
            }
            break;

        case ButtonPress: {
            Window clicked = ev.xbutton.subwindow ? ev.xbutton.subwindow : ev.xbutton.window;
            if (clicked == root) break;

            int mi = monforpt(ev.xbutton.x_root, ev.xbutton.y_root);
            Node *n = NULL;
            for (int i = 0; i < nmons && !n; i++) {
                if ((n = findleaf(mon_tree(i), clicked))) mi = i;
            }
            if (!n || (ev.xbutton.button != Button1 && ev.xbutton.button != Button3)) break;

            if (!n->real_fullscreen && !n->floating) {
                int fx = n->x + gap;
                int fy = n->y + gap;
                int fw = n->w - 2 * gap;
                int fh = n->h - 2 * gap;
                if (fw < 50) fw = 50;
                if (fh < 50) fh = 50;
                n->floating = 1;
                XMoveResizeWindow(dpy, n->win, fx, fy, fw - 2 * bw, fh - 2 * bw);
                retile();
            }

            if (n != mon_focused(mi)) setfocus(mi, n, 1);
            else {
                XRaiseWindow(dpy, n->win);
                raise_floating(mon_tree(mi));
            }

            {
                Window dw;
                unsigned gw, gh, gb, gd;
                XGetGeometry(dpy, n->win, &dw, &drag_wx, &drag_wy, &gw, &gh, &gb, &gd);
                drag_ww = (int)gw;
                drag_wh = (int)gh;
            }
            drag_ox = ev.xbutton.x_root;
            drag_oy = ev.xbutton.y_root;
            drag_node = n;
            drag_mon = mi;
            drag_mode = ev.xbutton.button == Button1 ? 1 : 2;

            XGrabPointer(dpy, root, False, PointerMotionMask | ButtonReleaseMask,
                GrabModeAsync, GrabModeAsync, None,
                drag_mode == 1 ? movecursor : resizecursor, CurrentTime);
            break;
        }

        case ButtonRelease:
            if (drag_mode) {
                XUngrabPointer(dpy, CurrentTime);
                if (drag_node) {
                    Window dw;
                    int rx, ry, wx2, wy2;
                    unsigned msk;
                    XQueryPointer(dpy, root, &dw, &dw, &rx, &ry, &wx2, &wy2, &msk);
                    int newmon = monforpt(rx, ry);
                    if (newmon != drag_mon) {
                        int was_floating = drag_node->floating;
                        detach(drag_mon, drag_node);
                        attach(newmon, drag_node);
                        drag_node->floating = was_floating;
                        curmon = newmon;
                        retile();
                    }
                }
            }
            drag_mode = 0;
            drag_node = NULL;
            drag_ww = drag_wh = 0;
            break;

        case MotionNotify:
            if (!drag_mode || !drag_node) break;
            {
                XEvent newer;
                while (XCheckTypedEvent(dpy, MotionNotify, &newer)) ev = newer;
            }
            {
                int dx = ev.xmotion.x_root - drag_ox;
                int dy = ev.xmotion.y_root - drag_oy;
                if (drag_mode == 1) {
                    int nx = drag_wx + dx;
                    int ny = drag_wy + dy;
                    if (nx < 0) nx = 0;
                    if (barpos == BAR_TOP && ny < barh) ny = barh;
                    if (barpos == BAR_BOTTOM && ny < 0) ny = 0;
                    if (nx + drag_ww + 2 * bw > sw) nx = sw - drag_ww - 2 * bw;
                    if (ny + drag_wh + 2 * bw > sh) ny = sh - drag_wh - 2 * bw;
                    XMoveWindow(dpy, drag_node->win, nx, ny);
                } else {
                    int nw = drag_ww + dx;
                    int nh = drag_wh + dy;
                    if (nw < 50) nw = 50;
                    if (nh < 50) nh = 50;
                    if (drag_wx + nw + 2 * bw > sw) nw = sw - drag_wx - 2 * bw;
                    if (drag_wy + nh + 2 * bw > sh) nh = sh - drag_wy - 2 * bw;
                    XResizeWindow(dpy, drag_node->win, nw, nh);
                }
            }
            break;

        case KeyPress: {
            unsigned int state = ev.xkey.state &
                (ShiftMask | ControlMask | Mod1Mask | Mod4Mask | LockMask | numlockmask);
            state &= ~(LockMask | numlockmask);
            KeySym sym = XLookupKeysym(&ev.xkey, 0);

            if (state == (ControlMask | Mod4Mask) && (sym == XK_Left || sym == XK_KP_Left)) {
                apply_wm_action("wm:swap_left");
                break;
            }
            if (state == (ControlMask | Mod4Mask) && (sym == XK_Right || sym == XK_KP_Right)) {
                apply_wm_action("wm:swap_right");
                break;
            }
            if (state == (ControlMask | Mod4Mask) && (sym == XK_Up || sym == XK_KP_Up)) {
                apply_wm_action("wm:swap_up");
                break;
            }
            if (state == (ControlMask | Mod4Mask) && (sym == XK_Down || sym == XK_KP_Down)) {
                apply_wm_action("wm:swap_down");
                break;
            }
            if (state == 0 && (sym == XK_Print || sym == XK_Sys_Req)) {
                apply_wm_action("wm:screenshot");
                break;
            }
            if (state == MOD && (sym == XK_Left || sym == XK_KP_Left)) {
                apply_wm_action("wm:focus_prev");
                break;
            }
            if (state == MOD && (sym == XK_Right || sym == XK_KP_Right)) {
                apply_wm_action("wm:focus_next");
                break;
            }
            if (state == MOD && (sym == XK_Up || sym == XK_KP_Up)) {
                apply_wm_action("wm:focus_up");
                break;
            }
            if (state == MOD && (sym == XK_Down || sym == XK_KP_Down)) {
                apply_wm_action("wm:focus_down");
                break;
            }

            int handled = 0;
            for (int i = 0; i < nmodbinds; i++) {
                if (ev.xkey.keycode == modbinds[i].code && state == modbinds[i].mod) {
                    handled = apply_wm_action(modbinds[i].action);
                    break;
                }
            }
            if (handled) break;

            if (mode == MODE_COMMAND) {
                handle_command_key(&ev.xkey, sym);
                break;
            }
            if (mode == MODE_NORMAL) {
                handle_normal_key(&ev.xkey, sym);
            }
            break;
        }
            }
        }
        drawbars_if_clock_changed();
        {
            struct timespec ts = {0, 100000000L};
            nanosleep(&ts, NULL);
        }
    }

    if (keyboard_grabbed) XUngrabKeyboard(dpy, CurrentTime);
    XCloseDisplay(dpy);
    return 0;
}
