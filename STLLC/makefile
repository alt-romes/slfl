build:
	cabal build
	noti cabal install --overwrite-policy=always # por isso tenho de fazer isto

run:
	# cabal run --opts mymodules/1.ll -- não consigo passar args
	STLLC mymodules/5.ll

test:
	./run-tests.sh

clean:
	cabal clean
