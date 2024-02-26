module Main where

import Test.Hspec
  ( hspec )
import qualified PropositionTests ( spec )

main :: IO ()
main = hspec $ do
  PropositionTests.spec
