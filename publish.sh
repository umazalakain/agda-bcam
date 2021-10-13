#!/bin/sh

git branch -f gh-pages main
git checkout gh-pages
agda --html --html-dir=agda Everything.agda
cabal new-run site build
git add agda docs
git commit -m "Update HTML pages"
git push origin gh-pages
git checkout main
