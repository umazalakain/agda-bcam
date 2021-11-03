--------------------------------------------------------------------------------
{-# LANGUAGE OverloadedStrings #-}

import Data.Monoid (mappend)
import Hakyll

--------------------------------------------------------------------------------
config :: Configuration
config =
  defaultConfiguration
    { destinationDirectory = "../docs"
    }

--------------------------------------------------------------------------------
main :: IO ()
main = hakyllWith config $ do
  match "agda/**" $ do
    route idRoute
    compile $
      getResourceBody
        >>= loadAndApplyTemplate "templates/tutorial-day.html" defaultContext
        >>= loadAndApplyTemplate "templates/default.html" defaultContext
        >>= relativizeUrls

  match ("favicon.ico" .||. "images/*.png" .||. "webfonts/*" .||. "talk.pdf") $ do
    route idRoute
    compile copyFileCompiler

  match "css/*" $ do
    route idRoute
    compile compressCssCompiler

  create ["tutorial.html"] $ do
    route idRoute
    compile $ do
      makeItem ""
        >>= loadAndApplyTemplate "templates/tutorial-default.html" defaultContext
        >>= loadAndApplyTemplate "templates/default.html" defaultContext
        >>= relativizeUrls

  create ["registration.html"] $ do
    route idRoute
    compile $ do
      makeItem ""
        >>= loadAndApplyTemplate "templates/registration.html" defaultContext
        >>= loadAndApplyTemplate "templates/default.html" defaultContext
        >>= relativizeUrls

  match "index.html" $ do
    route idRoute
    compile $ do
      getResourceBody
        >>= applyAsTemplate defaultContext
        >>= loadAndApplyTemplate "templates/default.html" defaultContext
        >>= relativizeUrls

  match "README.md" $ do
    route $ setExtension "html"
    compile $ do
      pandocCompiler
        >>= applyAsTemplate defaultContext
        >>= loadAndApplyTemplate "templates/default.html" defaultContext
        >>= relativizeUrls

  match "templates/*" $ compile templateBodyCompiler

--
--------------------------------------------------------------------------------
postCtx :: Context String
postCtx =
  dateField "date" "%B %e, %Y"
    <> defaultContext
