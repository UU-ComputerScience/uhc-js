# FLAGS = -tjscript --dump-core-stages=1 --dump-grin-stages=1 -O1,2 --gen-trace=1 --import-path=../../../uhc-jscript/src
#FLAGS = -tjs -Operwholecore --import-path=../../../uhc-jscript/src
FLAGS = -tjs --import-path=../../../uhc-jscript/src

ifndef PROJECT
  PROJECT = $(patsubst %.hs, %, $(wildcard *.hs))
endif

default: $(PROJECT).js

$(PROJECT).js: $(PROJECT).hs
	$(UHC) $(PROJECT).hs $(FLAGS)

clean:
	rm -f *.cr* *.hi $(PROJECT).js $(PROJECT).html *.mjs

.PHONY : clean strip
