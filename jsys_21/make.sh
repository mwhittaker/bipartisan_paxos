#! /usr/bin/env bash

set -euo pipefail

main() {
    latexmk -pdf rebuttal.tex
    latexmk -pdf ppaxos.tex
    pdfunite rebuttal.pdf ppaxos.pdf ppaxos_revisions.pdf
}

main "$@"
