.PHONY: build run test clean canonical canonical-init vscode-install vscode-uninstall

build:
	dune build

run: build
	@if [ -z "$(FILE)" ]; then \
	  echo "usage: make run FILE=examples/basic.mint"; exit 2; \
	fi
	./_build/default/src/mintc.bc.exe $(FILE)

# Run every example in `examples/`, one after another. Quick smoke test.
test: build
	@for f in examples/*.mint; do \
	  echo "============= $$f ============="; \
	  ./_build/default/src/mintc.bc.exe $$f || true; \
	  echo; \
	done

clean:
	dune clean

# === Canonical solver (vendor/Canonical) ============================
# The kernel-bridge `Mint.canonical` is currently stubbed; once it's
# wired in, it'll shell out to this binary.

canonical-init:
	git submodule update --init --recursive vendor/Canonical

CANONICAL_BIN := vendor/Canonical/target/release/canonical-compat
canonical:
	@if [ ! -d vendor/Canonical/.git ] && [ ! -f vendor/Canonical/.git ]; then \
	  echo "vendor/Canonical not initialized; run 'make canonical-init'"; exit 1; \
	fi
	cd vendor/Canonical && cargo build --release --bin canonical-compat
	@echo "Built: $(CANONICAL_BIN)"

# === VS Code extension ==============================================
# Install by symlinking vscode-mint/ into ~/.vscode/extensions. After
# install, reload VS Code (Cmd-Shift-P → Developer: Reload Window).
# The extension shells out to mintc, so `make build` first.

VSCODE_EXT_DIR := $(HOME)/.vscode/extensions/mint-lang-0.2.0
vscode-install: build
	@if [ -L "$(VSCODE_EXT_DIR)" ] || [ -e "$(VSCODE_EXT_DIR)" ]; then \
	  rm -rf "$(VSCODE_EXT_DIR)"; \
	fi
	ln -s "$(PWD)/vscode-mint" "$(VSCODE_EXT_DIR)"
	@echo "Installed: $(VSCODE_EXT_DIR) -> $(PWD)/vscode-mint"
	@echo "Reload VS Code (Cmd-Shift-P -> Developer: Reload Window) to activate."

vscode-uninstall:
	@if [ -L "$(VSCODE_EXT_DIR)" ] || [ -e "$(VSCODE_EXT_DIR)" ]; then \
	  rm -rf "$(VSCODE_EXT_DIR)"; \
	  echo "Removed: $(VSCODE_EXT_DIR)"; \
	else \
	  echo "Not installed: $(VSCODE_EXT_DIR)"; \
	fi
