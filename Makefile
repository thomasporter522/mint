make:
	cp -r ./content ./web/public
	cd web && npm run dev
	
init:
	cd web && npm install
