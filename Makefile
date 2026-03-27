make:
	cp -r ./content ./web/public
	$(MAKE) reason
	cd web && npm run dev

reason:
	cd reason && eval $$(opam env --switch=hazel) && dune build @reason

test:
	$(MAKE) reason
	cd web && npx vitest run

init:
	cd web && npm install
