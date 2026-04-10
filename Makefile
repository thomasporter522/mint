make:
	cp -r ./content ./web/public
	$(MAKE) reason
	cd web && npm run dev

.PHONY: reason clean
reason:
	cd reason && eval $$(opam env --switch=hazel) && dune build @reason

clean:
	cd reason && eval $$(opam env --switch=hazel) && dune clean

.PHONY: test
test:
	cp -r ./content ./web/public
	$(MAKE) reason
	cd web && npx vite build 2>&1 | tee /tmp/vite-build.log && \
		if grep -q 'is not exported by' /tmp/vite-build.log; then echo "BUILD ERROR: unresolved imports"; exit 1; fi
	cd web && npx vitest run

.PHONY: check try debug

check:
	$(MAKE) reason
	@node --no-warnings cli/check.mjs $(FILE)

.PHONY: try debug
try:
	$(MAKE) reason
	@node --no-warnings --input-type=module -e "import { parseAndPrint } from './reason/_build/default/src/output/src/Lytr_api.js'; console.log(parseAndPrint(process.argv[1]));" -- "$(EXPR)"

debug:
	$(MAKE) reason
	@node --no-warnings --input-type=module -e "import { parseAndDebug } from './reason/_build/default/src/output/src/Lytr_api.js'; console.log(parseAndDebug(process.argv[1]));" -- "$(EXPR)"

init:
	cd web && npm install
