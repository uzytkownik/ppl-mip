{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}
import Control.Lens
import Control.Lens.Extras
import Data.PPL.MIP
import Data.PPL.MIP.TH
import Test.QuickCheck

test1 :: Property
test1 = is _Optimized sl .&&.
        sl ^?! _Optimized . ix (var "x") === 100 .&&.
        sl ^?! _Optimized . ix (var "y") === 170
        where cs = sc 100 %<= var "x" %&& var "x" %<= sc 200 %&&
                   sc 80 %<= var "y" %&& var "y" %<= sc 170 %&&
                   var "y" %>= sc (-1) %* var "x" %+ sc 200
              o = Maximize $! sc (-2) %* var "x" %+ sc 5 %* var "y"
              ints = Integers []
              sl = mipSolve cs o ints

test2 :: Property
test2 = is _Optimized sl .&&.
        sl ^?! _Optimized . ix (var "x") === 1 .&&.
        sl ^?! _Optimized . ix (var "y") === 2
        where cs = sc 2 %* var "y" %>= sc 1 %+ sc 2 %* var "x" %&&
                   sc 10 %* var "y" %<= sc 13 %+ sc 8 %* var "x"
              o = Maximize $! var "x" %+ var "y"
              ints = Integers [var "x", var "y"]
              sl = mipSolve cs o ints

test3 :: Property
test3 = is _Optimized sl .&&.
        sl ^?! _Optimized . ix (var "x") === 4 .&&.
        sl ^?! _Optimized . ix (var "y") === 4.5
        where cs = sc 2 %* var "y" %>= sc 1 %+ sc 2 %* var "x" %&&
                   sc 10 %* var "y" %<= sc 13 %+ sc 8 %* var "x"
              o = Maximize $! var "x" %+ var "y"
              ints = Integers []
              sl = mipSolve cs o ints

test4 :: Property
test4 = property $ is _Unbounded sl
        where cs = var "x" %>= sc 0
              o = Maximize $! var "x"
              ints = Integers []
              sl = mipSolve cs o ints

test5 :: Property
test5 = property $ is _Unfeasable sl
        where cs = var "x" %>= sc 0 %&& var "x" %<= sc (-1)
              o = Maximize $! var "x"
              ints = Integers []
              sl = mipSolve cs o ints

test6 :: Property
test6 = is _Optimized sl .&&.
        sl ^?! _Optimized . ix (var "x") === 4 .&&.
        sl ^?! _Optimized . ix (var "y") === 4.5
        where cs = [affexp|2y|] %>= [affexp|2x + 1|] %&&
                   sc 10 %* var "y" %<= sc 13 %+ sc 8 %* var "x"
              o = Maximize $! [linexp|x + y|]
              ints = Integers []
              sl = mipSolve cs o ints

main :: IO ()
main = do
  quickCheck test1
  quickCheck test2
  quickCheck test3
  quickCheck test4
  quickCheck test5
  quickCheck test6
