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
#define MAXMONS       8
#define MAXWS         9
#define MAXAUTOSTART 8
#define CMDLINE_MAX 256

typedef struct Node Node;
struct Node {
    int leaf, floating, horiz;
    int fullscreen;
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
static ModBind modbinds[MAXBINDS];
static int nmodbinds;
static ModeBind normalbinds[MAXMODEBINDS];
static int nnormalbinds;
static CmdBind cmdbinds[MAXCMDS];
static int ncmdbinds;
static char autostart_cmds[MAXAUTOSTART][256];
static int nautostart;
static int modbind_limit = MAXBINDS;
static int normalbind_limit = MAXMODEBINDS;
static int cmd_limit = MAXCMDS;
static int autostart_limit = MAXAUTOSTART;
static GC bargc;
static XFontStruct *barfont;
static Cursor normalcursor;
static InputMode mode = MODE_INSERT;
static int keyboard_grabbed;
static int running = 1;
static unsigned int numlockmask;
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
static Node *mon_focused(int mi);
static void showtree(Node *n);
static void spawn(const char *cmd);
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
    static int last_battery_second = -1;
    time_t now = time(NULL);
    struct tm tm_now;
    const char *bases[] = {
        "/sys/class/power_supply/BAT0",
        "/sys/class/power_supply/BAT1",
        "/sys/class/power_supply/battery",
        NULL
    };
    char path[256], status[32], cap[32];
    FILE *f;

    localtime_r(&now, &tm_now);
    if (tm_now.tm_sec == last_battery_second) return;
    last_battery_second = tm_now.tm_sec;
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

static Node *findleaf(Node *n, Window w) {
    if (!n) return NULL;
    if (n->leaf) return n->win == w ? n : NULL;
    Node *r = findleaf(n->a, w);
    return r ? r : findleaf(n->b, w);
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
    if (n->leaf) return n->fullscreen ? n : NULL;
    r = find_fullscreen_leaf(n->a);
    return r ? r : find_fullscreen_leaf(n->b);
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
}

static void drawborder(Node *n, int focused) {
    XSetWindowBorderWidth(dpy, n->win, bw);
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

static void show_only_leaf(Node *n, Node *target) {
    if (!n) return;
    if (n->leaf) {
        if (n == target) XMapRaised(dpy, n->win);
        else XUnmapWindow(dpy, n->win);
        return;
    }
    show_only_leaf(n->a, target);
    show_only_leaf(n->b, target);
}

static void tilenode(Node *n, int x, int y, int w, int h, Node *foc) {
    if (!n) return;
    n->x = x;
    n->y = y;
    n->w = w;
    n->h = h;
    if (n->leaf) {
        drawborder(n, n == foc);
        if (n->fullscreen) {
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
    int pad = 8;
    int w = textw(text) + pad * 2;
    if (w < minw) w = minw;
    XSetForeground(dpy, bargc, bg);
    XFillRectangle(dpy, win, bargc, x, y, w, barh);
    XSetForeground(dpy, bargc, fg);
    XDrawString(dpy, win, bargc, x + pad, y + barh - 8, text, (int)strlen(text));
    return w;
}

static int section_width(const char *cfg) {
    char buf[128], *tok, *save;
    int width = 0;
    copystr(buf, sizeof buf, cfg);
    for (tok = strtok_r(buf, ",", &save); tok; tok = strtok_r(NULL, ",", &save)) {
        char item[128], tmp[256];
        copystr(item, sizeof item, ltrim(tok));
        rtrim(item);
        tmp[0] = 0;
        if (!strcasecmp(item, "workspaces")) {
            for (int i = 0; i < MAXWS; i++) {
                char part[8];
                if (!workspace_has_windows(i) && i != curws) continue;
                snprintf(part, sizeof part, "%d", i + 1);
                width += (textw(part) + 16) + 6;
            }
        } else if (!strcasecmp(item, "command")) {
            build_mode_text(tmp, sizeof tmp);
            width += textw(tmp) + 16;
            if (mode == MODE_COMMAND && cmdline_len > 0) width += 6 + textw(cmdline) + 16;
        } else if (!strcasecmp(item, "title")) {
            build_title_text(tmp, sizeof tmp);
            if (tmp[0]) width += textw(tmp) + 16;
        } else if (!strcasecmp(item, "clock")) {
            build_clock_text(tmp, sizeof tmp);
            width += textw(tmp) + 16;
        } else if (!strcasecmp(item, "battery")) {
            build_battery_text(tmp, sizeof tmp);
            if (tmp[0]) width += textw(tmp) + 16;
        } else if (!strcasecmp(item, "mode")) {
            build_mode_text(tmp, sizeof tmp);
            width += textw(tmp) + 16;
        }
    }
    return width > 0 ? width - 6 : 0;
}

static int draw_section(Window win, int x, int y, const char *cfg) {
    char buf[128], *tok, *save;
    int curx = x;
    copystr(buf, sizeof buf, cfg);
    for (tok = strtok_r(buf, ",", &save); tok; tok = strtok_r(NULL, ",", &save)) {
        char item[128], tmp[256];
        copystr(item, sizeof item, ltrim(tok));
        rtrim(item);
        if (!strcasecmp(item, "workspaces")) {
            for (int i = 0; i < MAXWS; i++) {
                char part[8];
                unsigned long bg = barbg, fg = barmutedfg;
                if (!workspace_has_windows(i) && i != curws) continue;
                snprintf(part, sizeof part, "%d", i + 1);
                if (i == curws) {
                    bg = cnorm;
                    fg = barfg;
                } else if (workspace_has_windows(i)) {
                    bg = barbg;
                    fg = barfg;
                }
                curx += draw_tag_box(win, curx, y, part, bg, fg, 20);
                curx += 6;
            }
        } else if (!strcasecmp(item, "command")) {
            build_mode_text(tmp, sizeof tmp);
            curx += draw_tag_box(win, curx, y, tmp, baraccentbg, baraccentfg, 0);
            if (mode == MODE_COMMAND && cmdline_len > 0) {
                curx += 6;
                curx += draw_tag_box(win, curx, y, cmdline, cnorm, barfg, 0);
            }
            curx += 6;
        } else if (!strcasecmp(item, "title")) {
            build_title_text(tmp, sizeof tmp);
            if (tmp[0]) {
                curx += draw_tag_box(win, curx, y, tmp, barbg, barfg, 0);
                curx += 6;
            }
        } else if (!strcasecmp(item, "clock")) {
            build_clock_text(tmp, sizeof tmp);
            curx += draw_tag_box(win, curx, y, tmp, baraccentbg, baraccentfg, 0);
            curx += 6;
        } else if (!strcasecmp(item, "battery")) {
            build_battery_text(tmp, sizeof tmp);
            if (tmp[0]) {
                curx += draw_tag_box(win, curx, y, tmp, cnorm, barfg, 0);
                curx += 6;
            }
        } else if (!strcasecmp(item, "mode")) {
            build_mode_text(tmp, sizeof tmp);
            curx += draw_tag_box(win, curx, y, tmp, baraccentbg, baraccentfg, 0);
            curx += 6;
        }
    }
    return curx;
}

static void drawbar(int mi) {
    if (!mons[mi].barwin) return;
    int leftx = 10, centx, rightx;
    int centerw = section_width(barcentercfg);
    int rightw = section_width(barrightcfg);

    XSetForeground(dpy, bargc, barbg);
    XFillRectangle(dpy, mons[mi].barwin, bargc, 0, 0, mons[mi].w, barh);

    draw_section(mons[mi].barwin, leftx, 0, barleftcfg);
    rightx = mons[mi].w - rightw - 10;
    if (rightw > 0) draw_section(mons[mi].barwin, rightx, 0, barrightcfg);
    centx = (mons[mi].w - centerw) / 2;
    if (centerw > 0 && centx > leftx + section_width(barleftcfg) + 12 && centx + centerw < rightx - 12)
        draw_section(mons[mi].barwin, centx, 0, barcentercfg);
}

static void drawbars_if_clock_changed(void) {
    time_t now = time(NULL);
    struct tm tm_now;
    localtime_r(&now, &tm_now);
    if (tm_now.tm_sec != last_clock_second) {
        drawbars();
    }
}

static void drawbars(void) {
    for (int i = 0; i < nmons; i++) drawbar(i);
    XSync(dpy, 0);
}

static void retile(void) {
    for (int i = 0; i < nmons; i++) {
        Mon *m = &mons[i];
        Node *fs = find_fullscreen_leaf(mon_tree(i));
        if (fs) {
            show_only_leaf(mon_tree(i), fs);
            drawborder(fs, fs == mon_focused(i));
            XMoveResizeWindow(dpy, fs->win, m->wx, m->wy, m->ww - 2 * bw, m->wh - 2 * bw);
            XRaiseWindow(dpy, fs->win);
        } else {
            showtree(mon_tree(i));
            tilenode(mon_tree(i), m->wx, m->wy, m->ww, m->wh, mon_focused(i));
            raise_floating(mon_tree(i));
        }
        if (m->barwin) XRaiseWindow(dpy, m->barwin);
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
    if (mons[mi].barwin) XRaiseWindow(dpy, mons[mi].barwin);
    if (warp) warpfocus(n);
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

static void hidetree(Node *n) {
    if (!n) return;
    if (n->leaf) {
        XUnmapWindow(dpy, n->win);
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
    if (mon_focused(curmon)) setfocus(curmon, mon_focused(curmon), 1);
}

static void attach_to_ws(int mi, int ws, Node *leaf) {
    leaf->par = NULL;
    if (!mon_tree_at(mi, ws)) {
        mon_settree_at(mi, ws, leaf);
        mon_setfocused_at(mi, ws, leaf);
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
}

static void attach(int mi, Node *leaf) { attach_to_ws(mi, curws, leaf); }

static void insert(int mi, Window w) { attach(mi, mkleaf(w)); }

static void detach_from_ws(int mi, int ws, Node *n) {
    if (!n->par) {
        mon_settree_at(mi, ws, NULL);
        mon_setfocused_at(mi, ws, NULL);
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
    return best;
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
    cfocus = 0x5588ff;
    cnorm = 0x333333;
    barbg = 0x111111;
    barfg = 0xeeeeee;
    baraccentbg = 0x5588ff;
    baraccentfg = 0x111111;
    barmutedfg = 0xaaaaaa;
    copystr(term, sizeof term, "st");
    copystr(barfontname, sizeof barfontname, "9x15");
    copystr(barleftcfg, sizeof barleftcfg, "workspaces");
    copystr(barcentercfg, sizeof barcentercfg, "command");
    copystr(barrightcfg, sizeof barrightcfg, "clock");
    barpos = BAR_TOP;
    nmodbinds = 0;
    nnormalbinds = 0;
    ncmdbinds = 0;
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

static void loadcfg(void) {
    const char *cfgpaths[] = {
        "/etc/viwm/config.conf",
        "./config.conf",
        NULL
    };

    reset_config_defaults();
    for (int i = 0; cfgpaths[i]; i++) {
        FILE *f = fopen(cfgpaths[i], "r");
        if (!f) continue;
        char line[512], k[64], v[448];
        while (fgets(line, sizeof line, f)) {
            char *p = ltrim(line);
            char mode_name[64], keyexpr[128], action[256];
            char cmd_name[64], cmd_action[256];
            if (!*p || *p == '#') continue;
            if (sscanf(p, "bind_%63[^ ] = %127[^=]= %255[^\n]", mode_name, keyexpr, action) == 3) {
                rtrim(mode_name);
                rtrim(keyexpr);
                rtrim(action);
                if (!strcasecmp(mode_name, "insert") && nmodbinds < modbind_limit) {
                    char *kp = strrchr(keyexpr, '+');
                    kp = kp ? kp + 1 : keyexpr;
                    kp = ltrim(kp);
                    if (*kp) {
                        KeySym sym = parse_keysym_name(kp);
                        if (sym != NoSymbol) {
                            KeyCode code = XKeysymToKeycode(dpy, sym);
                            if (code) {
                                modbinds[nmodbinds].mod = parse_mods(keyexpr);
                                modbinds[nmodbinds].code = code;
                                copystr(modbinds[nmodbinds].action, sizeof modbinds[nmodbinds].action, action);
                                nmodbinds++;
                            }
                        }
                    }
                } else if (!strcasecmp(mode_name, "normal") && nnormalbinds < normalbind_limit) {
                    KeySym sym = parse_keysym_name(keyexpr);
                    if (sym != NoSymbol) {
                        normalbinds[nnormalbinds].sym = sym;
                        copystr(normalbinds[nnormalbinds].action, sizeof normalbinds[nnormalbinds].action, action);
                        nnormalbinds++;
                    }
                }
                continue;
            }
            if (sscanf(p, "command = %63[^=]= %255[^\n]", cmd_name, cmd_action) == 2) {
                rtrim(cmd_name);
                rtrim(cmd_action);
                if (ncmdbinds < cmd_limit) {
                    copystr(cmdbinds[ncmdbinds].name, sizeof cmdbinds[ncmdbinds].name,
                        skip_command_prefix(cmd_name));
                    copystr(cmdbinds[ncmdbinds].action, sizeof cmdbinds[ncmdbinds].action, cmd_action);
                    ncmdbinds++;
                }
                continue;
            }
            {
                char *eq = strchr(p, '=');
                if (!eq) continue;
                *eq = 0;
                copystr(k, sizeof k, ltrim(p));
                rtrim(k);
                copystr(v, sizeof v, ltrim(eq + 1));
                rtrim(v);
            }
            if (!strcmp(k, "autostart")) {
                if (nautostart < autostart_limit && v[0]) {
                    copystr(autostart_cmds[nautostart], sizeof autostart_cmds[nautostart], v);
                    nautostart++;
                }
                continue;
            }
            if (!strcmp(k, "insert_bind_limit")) {
                modbind_limit = clampi(atoi(v), 1, MAXBINDS);
                continue;
            }
            if (!strcmp(k, "normal_bind_limit")) {
                normalbind_limit = clampi(atoi(v), 1, MAXMODEBINDS);
                continue;
            }
            if (!strcmp(k, "command_limit")) {
                cmd_limit = clampi(atoi(v), 1, MAXCMDS);
                continue;
            }
            if (!strcmp(k, "autostart_limit")) {
                autostart_limit = clampi(atoi(v), 1, MAXAUTOSTART);
                continue;
            }
            if (!strcmp(k, "gap")) gap = atoi(v);
            else if (!strcmp(k, "border")) bw = atoi(v);
            else if (!strcmp(k, "bar_height")) barh = atoi(v);
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
            }
            else if (!strcmp(k, "terminal")) copystr(term, sizeof term, v);
        }
        fclose(f);
        break;
    }
}

static void run_autostart(void) {
    for (int i = 0; i < nautostart; i++) spawn(autostart_cmds[i]);
}

static void set_net_wm_state(Window win, int fullscreen) {
    Atom state = XInternAtom(dpy, "_NET_WM_STATE", False);
    Atom fs = XInternAtom(dpy, "_NET_WM_STATE_FULLSCREEN", False);
    if (fullscreen) {
        Atom atoms[1] = { fs };
        XChangeProperty(dpy, win, state, XA_ATOM, 32, PropModeReplace, (unsigned char *)atoms, 1);
    } else {
        XDeleteProperty(dpy, win, state);
    }
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
        if (mon_focused(curmon)->fullscreen) mon_focused(curmon)->floating = 0;
        set_net_wm_state(mon_focused(curmon)->win, mon_focused(curmon)->fullscreen);
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
    if (cmdline_len < 2 || cmdline[0] != ':') {
        enter_mode(MODE_NORMAL);
        return 0;
    }
    const char *name = cmdline + 1;
    for (int i = 0; i < ncmdbinds; i++) {
        if (!strcmp(name, cmdbinds[i].name)) {
            int keep = apply_wm_action(cmdbinds[i].action);
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
        copystr(cmdline, sizeof cmdline, ":");
        cmdline_len = 1;
        enter_mode(MODE_COMMAND);
        return 1;
    }
    if (sym == XK_Escape) {
        enter_mode(MODE_INSERT);
        return 1;
    }
    if (sym == XK_Left) return apply_wm_action("wm:focus_prev");
    if (sym == XK_Right) return apply_wm_action("wm:focus_next");
    for (int i = 0; i < nnormalbinds; i++) {
        if (normalbinds[i].sym == sym) {
            return apply_wm_action(normalbinds[i].action);
        }
    }
    return 0;
}

static void setupbars(void) {
    XGCValues gcv;
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
            m->barwin = XCreateSimpleWindow(dpy, root, m->x, m->y, m->w, barh, 0, barbg, barbg);
        } else {
            m->wy = m->y;
            m->barwin = XCreateSimpleWindow(dpy, root, m->x, m->y + m->h - barh, m->w, barh, 0, barbg, barbg);
        }
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
    XDefineCursor(dpy, root, normalcursor);

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
        GrabModeSync, GrabModeAsync, None, None);
    XGrabButton(dpy, Button3, MOD, root, False,
        ButtonPressMask | ButtonReleaseMask,
        GrabModeSync, GrabModeAsync, None, None);

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
            XSelectInput(dpy, ev.xmaprequest.window, EnterWindowMask);
            XMapWindow(dpy, ev.xmaprequest.window);
            {
                Window dw;
                int rx, ry, wx, wy;
                unsigned msk;
                XQueryPointer(dpy, root, &dw, &dw, &rx, &ry, &wx, &wy, &msk);
                int mi = monforpt(rx, ry);
                insert(mi, ev.xmaprequest.window);
                retile();
                setfocus(mi, mon_focused(mi), 1);
            }
            break;

        case DestroyNotify:
            removewin(ev.xdestroywindow.window);
            retile();
            if (mon_focused(curmon)) setfocus(curmon, mon_focused(curmon), 0);
            break;

        case UnmapNotify:
            if (ev.xunmap.send_event) {
                removewin(ev.xunmap.window);
                retile();
                if (mon_focused(curmon)) setfocus(curmon, mon_focused(curmon), 0);
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
            if (clicked == root) {
                XAllowEvents(dpy, ReplayPointer, ev.xbutton.time);
                break;
            }

            int mi = monforpt(ev.xbutton.x_root, ev.xbutton.y_root);
            Node *n = NULL;
            for (int i = 0; i < nmons && !n; i++) {
                if ((n = findleaf(mon_tree(i), clicked))) mi = i;
            }

            if (n && n->floating) {
                XAllowEvents(dpy, AsyncPointer, ev.xbutton.time);
                if (n != mon_focused(mi)) setfocus(mi, n, 1);
                else {
                    XRaiseWindow(dpy, n->win);
                    raise_floating(mon_tree(mi));
                }

                Window dw;
                unsigned gw, gh, gb, gd;
                XGetGeometry(dpy, n->win, &dw, &drag_wx, &drag_wy, &gw, &gh, &gb, &gd);
                drag_ww = (int)gw;
                drag_wh = (int)gh;
                drag_ox = ev.xbutton.x_root;
                drag_oy = ev.xbutton.y_root;
                drag_node = n;
                drag_mon = mi;
                drag_mode = ev.xbutton.button == Button1 ? 1 : 2;

                XGrabPointer(dpy, root, False, PointerMotionMask | ButtonReleaseMask,
                    GrabModeAsync, GrabModeAsync, None, None, CurrentTime);
            } else {
                XAllowEvents(dpy, ReplayPointer, ev.xbutton.time);
                if (n && n != mon_focused(mi)) {
                    setfocus(mi, n, 1);
                    retile();
                } else if (n) {
                    XRaiseWindow(dpy, n->win);
                }
            }
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
                    if (ny < barh) ny = barh;
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

            if (state == (ControlMask | Mod4Mask) && sym == XK_Left) {
                apply_wm_action("wm:swap_prev");
                break;
            }
            if (state == (ControlMask | Mod4Mask) && sym == XK_Right) {
                apply_wm_action("wm:swap_next");
                break;
            }
            if (state == 0 && (sym == XK_Print || sym == XK_Sys_Req)) {
                apply_wm_action("wm:screenshot");
                break;
            }
            if (state == MOD && sym == XK_Left) {
                apply_wm_action("wm:focus_prev");
                break;
            }
            if (state == MOD && sym == XK_Right) {
                apply_wm_action("wm:focus_next");
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
