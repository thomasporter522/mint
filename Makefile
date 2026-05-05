make:
	cp -r ./content ./web/public
	$(MAKE) reason
	cd web && npm run dev

.PHONY: reason clean grammar
grammar:
	cd web && npm run build-grammar

reason:
	cd reason && eval $$(opam env --switch=hazel) && dune build @reason

clean:
	cd reason && eval $$(opam env --switch=hazel) && dune clean

.PHONY: test
test:
	cp -r ./content ./web/public
	$(MAKE) grammar
	$(MAKE) reason
	cd web && npx vite build 2>&1 | tee /tmp/vite-build.log && \
		if grep -q 'is not exported by' /tmp/vite-build.log; then echo "BUILD ERROR: unresolved imports"; exit 1; fi
	cd web && npx vitest run

.PHONY: check try debug

check:
	$(MAKE) grammar
	$(MAKE) reason
	@node --no-warnings --experimental-strip-types cli/check.mjs $(FILE)

.PHONY: try debug
try:
	$(MAKE) grammar
	$(MAKE) reason
	@node --no-warnings --experimental-strip-types --input-type=module -e "import { parseAndPrint } from './web/src/lytr/reason-bridge.ts'; console.log(parseAndPrint(process.argv[1]));" -- "$(EXPR)"

# `parseAndDebug` is gone; the new architecture's debug equivalent is
# the Lezer tree, which can be inspected via tests or the grammar build.
debug:
	@echo "make debug is currently unwired (parseAndDebug was removed in the parser swap). Inspect the Lezer tree via web/src/lytr/grammar/__tests__/diagnose.test.ts if needed."

.PHONY: init vscode-init vscode-build vscode-smoke vscode-install vscode-uninstall
init:
	cd web && npm install

vscode-init:
	cd vscode-mint && npm install

# Build the VS Code extension. Depends on the grammar and OCaml output
# because esbuild bundles them into the extension binary.
vscode-build:
	$(MAKE) grammar
	$(MAKE) reason
	cd vscode-mint && npm run build

# Smoke-test the bundled extension by loading it with a mocked vscode host
# and verifying processCode flows through.
vscode-smoke:
	$(MAKE) vscode-build
	cd vscode-mint && node --no-warnings --experimental-strip-types test-bundle.mjs

# Install the extension permanently into VS Code by symlinking the
# vscode-mint directory under ~/.vscode/extensions. Restart VS Code
# (or reload the window) once after installing.
VSCODE_EXT_DIR := $(HOME)/.vscode/extensions/mint-lang-0.1.0
vscode-install:
	$(MAKE) vscode-build
	@if [ -L "$(VSCODE_EXT_DIR)" ] || [ -e "$(VSCODE_EXT_DIR)" ]; then \
		rm -rf "$(VSCODE_EXT_DIR)"; \
	fi
	ln -s "$(PWD)/vscode-mint" "$(VSCODE_EXT_DIR)"
	@echo "Installed: $(VSCODE_EXT_DIR) -> $(PWD)/vscode-mint"
	@echo "Reload VS Code (Cmd-Shift-P → Developer: Reload Window) to activate."

vscode-uninstall:
	@if [ -L "$(VSCODE_EXT_DIR)" ] || [ -e "$(VSCODE_EXT_DIR)" ]; then \
		rm -rf "$(VSCODE_EXT_DIR)"; \
		echo "Removed: $(VSCODE_EXT_DIR)"; \
	else \
		echo "Not installed: $(VSCODE_EXT_DIR)"; \
	fi
