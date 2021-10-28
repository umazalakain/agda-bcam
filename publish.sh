#!/bin/sh

git branch -f gh-pages main
git checkout gh-pages
agda --html --html-dir=html Everything.agda
git add html
git commit -m "Update HTML pages"
git push -f origin gh-pages
git checkout main
