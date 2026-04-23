CC      = cc
CFLAGS  = -Os -std=c99 -Wall -Wextra -pedantic -flto
LDFLAGS = -lX11 -lXinerama
BIN     = viwm
SRC     = viwm.c

$(BIN): $(SRC)
	$(CC) $(CFLAGS) -o $(BIN) $(SRC) $(LDFLAGS)

install: $(BIN)
	install -Dm755 $(BIN)       /usr/local/bin/$(BIN)
	install -Dm644 config.conf  /etc/viwm/config.conf

uninstall:
	rm -f /usr/local/bin/$(BIN)
	rm -f /etc/viwm/config.conf

clean:
	rm -f $(BIN)

.PHONY: install uninstall clean
