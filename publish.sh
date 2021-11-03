#!/bin/sh

git branch -f gh-pages main
git checkout gh-pages
agda --html --html-dir=site/agda Everything.agda
(cd Talk; pdflatex talk.tex; cp talk.pdf ../site/talk.pdf)
(cd site; cabal new-run site build)
git add -f site/agda docs
git commit -m "Update HTML pages"
git push -f origin gh-pages
git checkout main
