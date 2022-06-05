# literally just convenience

.PHONY: build

build:
	idris2 --build managed.ipkg

install:
	idris2 --install managed.ipkg

clean:
	@find . -type f -name '*.ttc' -exec rm -f {} \;
	@find . -type f -name '*.ttm' -exec rm -f {} \;
	@find . -type f -name '*.ibc' -exec rm -f {} \;
