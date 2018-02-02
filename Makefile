screen-size.js: screen-size.hs
	hastec -O3 -Wall -fno-warn-unused-do-bind screen-size.hs
	mkdir -p dist
	cp screen-size.js dist
	cp screen-*.svg dist
	cp screen-size.css dist
	cp screen-size.html dist

clean:
	rm Main.jsmod screen-size.js screen-size.o screen-size.hi

