#!/bin/sh

git branch -f gh-pages main
git checkout gh-pages
agda --html --html-dir=site/agda Everything.agda
(cd site; cabal new-run site build)
git add site/agda docs
git commit -m "Update HTML pages"
git push -f origin gh-pages
git checkout main
