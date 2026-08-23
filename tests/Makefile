AGDA_EXEC        ?= agda
GHC_EXEC         ?= ghc
AGDA_OPTIONS     ?=
AGDA_RTS_OPTIONS ?= +RTS -M4.0G -H3.5G -A128M -RTS
AGDA             ?= $(AGDA_EXEC) $(AGDA_OPTIONS) $(AGDA_RTS_OPTIONS)
INTERACTIVE      ?= --interactive
CABAL            ?= cabal
CABAL_OPTIONS    ?= --with-compiler $(GHC_EXEC)

AGDA_BUILD_DIR  = _config/_build
CABAL_BUILD_DIR = _config/dist-newstyle

./runtests: admin/runtests/Main.agda
	cd admin/runtests && AGDA="$(AGDA)" sh run

test: ./runtests
	./runtests "$(AGDA)" $(INTERACTIVE) --timing --failure-file failures --only $(only)


retest: ./runtests
	./runtests "$(AGDA)" $(INTERACTIVE) --timing --failure-file failures --only-file failures --only $(only)

clean:
	rm -rf runtests
	rm -rf _config/_build
	rm -rf _config/dist-newstyle
