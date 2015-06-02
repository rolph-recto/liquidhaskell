THREADS=1
SMTSOLVER=z3

FASTOPTS="-O0"
DISTOPTS="-W -O2 -XStandaloneDeriving"
PROFOPTS="-O2 -rtsopts -prof -auto-all -caf-all -XStandaloneDeriving -XDeriveDataTypeable"
LIQUIDOPTS=""

CABAL=cabal
CABALI=$(CABAL) install --ghc-options=$(OPTS)
CABALP=$(CABAL) install --ghc-options=$(OPTS) -p

# to deal with cabal sandboxes using dist/dist-sandbox-xxxxxx/build/test/test
# TASTY=find dist -type f -name test | head -n1
TASTY=./dist/build/test/test

DEPS=unix-compat transformers mtl filemanip text parsec ghc-paths deepseq comonad contravariant semigroupoids semigroups bifunctors hscolour ansi-terminal hashable unordered-containers

##############################################################################
##############################################################################
##############################################################################

fast:
	$(CABAL) install -fdevel --ghc-options=$(FASTOPTS) 

debug-fixpoint:
	# deregister and then reregister liquid-fixpoint
	# I have no idea why this is necessary
	# but Cabal throws a fit otherwise
	$(CABAL) sandbox delete-source ../liquid-fixpoint
	$(CABAL) sandbox hc-pkg -- unregister liquid-fixpoint --force
	$(CABAL) sandbox add-source ../liquid-fixpoint

first: 
	$(CABAL) install --ghc-options=$(FASTOPTS) --only-dependencies --enable-tests --enable-benchmarks

dist:
	$(CABAL) install --ghc-options=$(DISTOPTS) 

prof:
	$(CABAL) install --enable-executable-profiling --enable-library-profiling --ghc-options=$(PROFOPTS) 

igotgoto:
	$(CABAL) build --ghc-options=$(OPTS) 
	cp dist/build/liquid/liquid ~/.cabal/bin/

copy-binaries:
	cp .cabal-sandbox/bin/fixpoint ~/.cabal/bin/
	cp .cabal-sandbox/bin/fixpoint.native ~/.cabal/bin/
	cp .cabal-sandbox/bin/liquid ~/.cabal/bin/

debug-install:
	$(CABAL) install --ghc-options=$(FASTOPTS) 
	cp .cabal-sandbox/bin/fixpoint ~/.cabal/bin/
	cp .cabal-sandbox/bin/fixpoint.native ~/.cabal/bin/
	cp .cabal-sandbox/bin/liquid ~/.cabal/bin/

clean:
	cabal clean

docs:
	$(CABAL) hscolour
	$(CABAL) haddock --hoogle

deps:
	$(CABALI) $(DEPS)

pdeps:
	$(CABALP) $(DEPS)

all-test-py:
	cd tests && ./regrtest.py -a -t $(THREADS) && cd ../

test-py:
	cd tests && ./regrtest.py -t $(THREADS) && cd ../

test:
	$(CABAL) configure -fdevel --enable-tests --disable-library-profiling -O2
	$(CABAL) build
	$(CABAL) exec $(TASTY) -- --smtsolver $(SMTSOLVER) --hide-successes --rerun-update -p 'Unit/' -j$(THREADS) +RTS -N$(THREADS) -RTS
	# $(CABAL) exec $(TASTY) -- --smtsolver $(SMTSOLVER) --liquid-opts='$(LIQUIDOPTS)' --hide-successes --rerun-update -p 'Unit/' -j$(THREADS) +RTS -N$(THREADS) -RTS


retest:
	cabal configure -fdevel --enable-tests --disable-library-profiling -O2
	cabal build
	cabal exec $(TASTY) -- --smtsolver $(SMTSOLVER) --hide-successes --rerun-filter "exceptions,failures,new" --rerun-update -p 'Unit/' -j$(THREADS) +RTS -N$(THREADS) -RTS

all-test:
	cabal configure -fdevel --enable-tests --disable-library-profiling -O2
	cabal build
	cabal exec $(TASTY) -- --smtsolver $(SMTSOLVER) --hide-successes --rerun-update -j$(THREADS) +RTS -N$(THREADS) -RTS

all-retest:
	cabal configure -fdevel --enable-tests --disable-library-profiling -O2
	cabal build
	cabal exec $(TASTY) -- --smtsolver $(SMTSOLVER) --hide-successes --rerun-filter "exceptions,failures,new" --rerun-update -j$(THREADS) +RTS -N$(THREADS) -RTS

lint:
	hlint --colour --report .

tags:
	hasktags -c src/
	hasktags -e src/
