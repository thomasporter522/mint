make:
	cp -r ./content ./web/public
	$(MAKE) reason
	cd web && npm run dev

.PHONY: reason
reason:
	cd reason && eval $$(opam env --switch=hazel) && dune build @reason

.PHONY: test
test:
	$(MAKE) reason
	cd web && npx vite build 2>&1 | tee /tmp/vite-build.log && \
		if grep -q 'is not exported by' /tmp/vite-build.log; then echo "BUILD ERROR: unresolved imports"; exit 1; fi
	cd web && npx vitest run

init:
	cd web && npm install
