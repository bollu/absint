#!/usr/bin/env bash
ghcid -o ghcid.txt -c "cabal v2-repl --extra-lib-dirs=/usr/local/lib --extra-include-dirs=/usr/local/include --extra-lib-dirs=/usr/lib/x86_64-linux-gnu/"
