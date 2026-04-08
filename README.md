# VIWM

Vim-inspired tiling window manager for X11.

VIWM uses a modal workflow:

- `INSERT` for normal desktop input
- `NORMAL` for window-manager actions
- `COMMAND` for vim-style commands such as `:q!`

Windows are managed in a simple tiling tree. New windows are attached near the focused one. Floating windows stay above tiled ones and can be moved or resized freely. Multi-monitor setups are handled through Xinerama.

## Dependencies

- `libX11`
- `libXinerama`
- C99 compiler

Examples:

- Arch Linux: `sudo pacman -S libx11 libxinerama`
- Artix Linux: `sudo pacman -S libx11 libxinerama`
- Void Linux: `sudo xbps-install libX11-devel libxinerama-devel`
- Gentoo: `emerge x11-libs/libX11 x11-libs/libXinerama`
- Debian / Ubuntu: `sudo apt install libx11-dev libxinerama-dev build-essential`
- Fedora: `sudo dnf install libX11-devel libXinerama-devel gcc make`
- openSUSE: `sudo zypper install libX11-devel libXinerama-devel gcc make`
- Alpine: `sudo apk add libx11-dev libxinerama-dev build-base`

## Build

```
make
sudo make install
```

Add to `~/.xinitrc`:

```
exec viwm
```

## Greeter / XSession Example

If you want to add VIWM to your greeter, one simple setup looks like this:

`/usr/share/xsessions/viwm.desktop`

```ini
[Desktop Entry]
Name=VIWM
Comment=Vim Window Manager
Exec=/usr/local/bin/viwm-session
Type=XSession
DesktopNames=viwm
```

`/usr/local/bin/viwm-session`

```
#!/bin/sh
export XDG_CURRENT_DESKTOP=viwm
export XDG_SESSION_DESKTOP=viwm
export XDG_SESSION_TYPE=x11

exec dbus-run-session sh -lc '
  /usr/local/bin/ensure-audio-session
  exec viwm
'
```

## Configuration

`/etc/viwm/config.conf` or `./config.conf`. No recompile needed.

Example:

```conf
gap            = 8
border         = 2
bar_height     = 24
bar_position   = bottom
border_focus   = 7aa2f7
border_normal  = 2f3549
terminal       = st

bind_insert = mod+Space = spawn:rofi -show drun
bind_insert = mod+1 = wm:workspace:1
bind_normal = i = wm:mode:insert
command = :q! = wm:quit
```

Supported modifiers:

- `mod` = Super
- `shift`
- `ctrl`
- `alt`

## Bar

The bar is split into three sections:

- `bar_left`
- `bar_center`
- `bar_right`

Available elements:

- `command`
- `title`
- `workspaces`
- `battery`
- `clock`
- `mode`

Example:

```conf
bar_left   = command,title
bar_center =
bar_right  = workspaces,battery,clock
```

## Modes

### INSERT

Applications receive keyboard input normally.

### NORMAL

Window-manager keys are handled directly.

Default pattern:

- `Super+Escape` enters `NORMAL`
- `i` returns to `INSERT`
- `:` enters `COMMAND`

### COMMAND

Commands are typed in the bar and executed with `Enter`.

Example:

```text
:q!
```

## Keybinds

The exact behavior depends on your config, but the default setup includes:

| Key | Action |
| --- | --- |
| `Super+Escape` | Enter `NORMAL` mode |
| `i` | Return to `INSERT` mode |
| `:` | Enter `COMMAND` mode |
| `Super+1..9` | Switch workspace |
| `Super+Left/Right` | Focus previous / next window |
| `Super+Ctrl+Left/Right` | Swap with previous / next window |
| `Super+j / Super+k` | Focus down / up |
| `j / k` | Focus down / up in `NORMAL` |
| `h / l` | Shrink / grow split |
| `f` | Toggle floating |
| `v` | Flip split orientation |
| `:q!` | Quit VIWM |

## Floating

Floating windows stay above tiled ones.

- toggle floating from `NORMAL` mode
- drag with `mod+Button1`
- resize with `mod+Button3`

Dragging a floating window to another monitor moves it to that monitor.

## Workspaces

VIWM provides workspaces `1..9`.

- each monitor keeps its own tree per workspace
- switching workspace only shows windows from that workspace
- focused windows can be moved to another workspace from keybinds

## Multi-Monitor

Each monitor keeps its own independent layout tree.

- new windows open on the monitor under the pointer
- focus and tiling stay local to that monitor
- floating windows can move across monitor boundaries

## Notes

- `config.conf` is the main configuration file
- media and brightness keys are optional and can be added from config
- the project is still experimental
