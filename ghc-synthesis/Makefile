Main Main.hi Main.o: Main.hs Plugin.dyn_o
	ghc -package ghc $<
Plugin.o Plugin.hi Plugin.dyn_o Plugin.dyn_hi: Plugin.hs
	ghc -package ghc -c -dynamic-too $<

.PHONY: clean
clean:
	rm -f Main Main.o Main.hi Plugin.o Plugin.hi Plugin.dyn_o Plugin.dyn_hi
