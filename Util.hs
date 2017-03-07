module Util where

import Data.Maybe
import Data.Bits (Bits,testBit)
import Data.List (partition,sortOn)
import Control.Arrow ((***))

bools :: Bits b => b -> [Bool]
bools b = map (testBit b) [0..]

bitFilter :: Bits b => b -> [a] -> [a]
bitFilter bits = map snd . filter fst . zip (bools bits)

partitionEvery :: Int -> [a] -> ([a],[a])
partitionEvery 0 = \x -> (x,[])
partitionEvery n = (map snd *** map snd) . partition ((0==) . (`mod` n) . fst) . zip [0..]

closest :: (Ord a, Num a) => a -> [a] -> [a]
closest a = map fst . sortOn snd . map (\x -> (x,abs (a-x)))

weightedIterate :: [[a]] -> [a]
weightedIterate opts = concat now ++ weightedIterate later
  where len = length opts
        (now,later) = unzip $ zipWith (\i -> splitAt (len - i)) [0..] opts