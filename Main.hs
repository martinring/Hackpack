module Main where

import Util
import System.Random (RandomGen,mkStdGen,randomR)
import System.Exit (die)
import Control.Applicative ((<|>))
import Control.Arrow ((***))
import Control.Concurrent (putMVar,takeMVar,forkIO,newEmptyMVar)
import Control.Monad (when)
import Data.Bits (Bits,popCount,shiftL)
import Data.Bits.Bitwise (fromListLE)
import Data.Array (Array,listArray,bounds,(!),indices)
import Data.List (find,delete,sortOn,unfoldr,(\\),sort,foldl',minimumBy)
import Data.Maybe (listToMaybe,maybeToList,isJust,mapMaybe,fromJust)
import System.Environment (getArgs)
import qualified Data.Map as Map

data SearchType = IncludedSearch
                | SubsetSearch
                | RandomMutate
                | NaiveSearch deriving Show

data Subset = BinarySubset { items :: [Integer] }
            | ExplicitSubset { items :: [Integer], explicitArray :: Array Int [Integer] }

instance Show Subset where
  show (BinarySubset items) = "Binary " ++ show items
  show (ExplicitSubset items arr) = "Explicit " ++ show items

maxValue :: Subset -> Integer
maxValue s = value (size s - 1) s

size :: Subset -> Int
size (BinarySubset xs) = 2 ^ length xs
size (ExplicitSubset _ arr) = 1 + snd (bounds arr)

values :: Int -> Subset -> [Integer]
values n (BinarySubset xs) = bitFilter n xs
values n (ExplicitSubset _ arr) = arr ! n

unvalues :: [Integer] -> Subset -> Int
unvalues is (BinarySubset items) = fromListLE $ snd $ foldr (\x (is,r) -> (delete x is,elem x is:r)) (is,[]) items
unvalues is (ExplicitSubset items arr) = fromJust $ find ((==selection) . (arr !)) $ indices arr
  where selection = snd $ foldr (\x (is,r) -> (delete x is,if elem x is then x:r else r)) (is,[]) items

value :: Int -> Subset -> Integer
value n = sum . values n

explicitSubset :: [Integer] -> Subset
explicitSubset items = ExplicitSubset items $ listArray (0,lastIndex) entries
  where entries = sortOn sum $ map (flip bitFilter items) [0..lastIndex]
        lastIndex = (2 ^ length items - 1) :: Int


extractBinarySubset :: [Integer] -> Maybe (Subset,[Integer])
extractBinarySubset = filterMaybe . rev. extractSubset
  where filterMaybe (i,e) = if length i >= 8 then Just (BinarySubset i,e) else Nothing
        rev = reverse *** reverse
        extractSubset = foldl (\(i,e) el -> if sum i <= el then (el:i,e) else (i,el:e)) ([],[])

extractExplicitSubset :: [Integer] -> Maybe (Subset,[Integer])
extractExplicitSubset []    = Nothing
extractExplicitSubset items = Just (explicitSubset i, e)
  where (i,e) = partitionEvery k items
        k = 1 + (length items `div` 10)

extractSubset :: [Integer] -> Maybe (Subset,[Integer])
extractSubset items = extractBinarySubset items <|> extractExplicitSubset items

extractSubsets :: [Integer] -> [Subset]
extractSubsets = unfoldr extractSubset

findNearest :: Integer -> Subset -> Int
findNearest target s = findr 0 $ size s
  where findr min max
         | v < target && p > min = findr p max
         | v > target && p < max = findr min p
         | otherwise             = p
           where p = min + (max - min) `div` 2
                 v = value p s

vectorValues :: [Int] -> [Subset] -> [Integer]
vectorValues ns = concatMap (uncurry values) . zip ns

vectorValue :: [Int] -> [Subset] -> Integer
vectorValue ns = sum . zipWith value ns

dropEqualBy :: Ord b => (a -> b) -> [a] -> [a]
dropEqualBy f = foldr consIfDifferent []
  where consIfDifferent x [] = [x]
        consIfDifferent x (y:ys) = if f x == f y then y:ys else x:y:ys

alternate :: [a] -> [a] -> [a]
alternate (x:xs) ys = x : alternate ys xs
alternate _ ys = ys

startVector :: Integer -> [Subset] -> [Int]
startVector target subsets = snd $ unzip $ tail $ scanl scanf ((max,target),0) subsets
  where max = sum $ map maxValue subsets
        scanf ((total,target),i) subset = ((total - maxValue subset, target - value nearest subset), nearest)
          where nearest = findNearest ((target * maxValue subset) `div` total) subset

selectionAsVector :: [Integer] -> [Subset] -> [Int]
selectionAsVector items []     = []
selectionAsVector items (s:ss) = i : selectionAsVector r ss
  where i = unvalues items s
        r = items \\ (values i s)

startVectorBySize :: Integer ->  [Subset] -> Int -> [Int]
startVectorBySize target subsets k = selectionAsVector selected subsets
  where selected = itemSelectionBySize target k (concatMap items subsets)

itemSelectionBySize :: Integer -> Int -> [Integer] -> [Integer]
itemSelectionBySize target k [] = []
itemSelectionBySize target k items = if k <= 0 then [] else selected : (itemSelectionBySize (target - selected) (k - 1) remaining)
  where (selected:remaining) = closest (target `div` (toInteger k)) items

equalAlternatives :: Int -> Subset -> [Int]
equalAlternatives p xs = alternate lower higher
  where lower  = takeWhile (\p -> v == value p xs) $ takeWhile (>=0) $ map (p-) [0..]
        higher = takeWhile (\p -> v == value p xs) $ takeWhile (< max) $ map (p+) [1..]
        v      = value p xs
        max    = size xs

alternatives :: Int -> Subset -> [Int]
alternatives p xs = alternate lower higher
  where lower  = dropEqualBy (flip value xs) $ takeWhile (>=0) $ map (p-) [0..]
        higher = dropEqualBy (flip value xs) $ takeWhile (< max) $ map (p+) [1..]
        max    = size xs

alternativesTree :: [[Int]] -> [([Int],[[Int]])]
alternativesTree [] = []
alternativesTree ([x,y]:ys) = (y:map head ys,[y]:ys) : map (\(z,as) -> (x:z,(x:y:[]):as)) (alternativesTree ys)
alternativesTree ((x:y:xs):ys) = (y:map head ys,(xs):ys) : map (\(z,as) -> (x:z,(x:y:xs):as)) (alternativesTree ys)
alternativesTree ([x]:ys) = map (\(y,as) -> (x:y,[x]:as)) $ alternativesTree ys

breadthFirstAlternatives :: [[Int]] -> [[Int]]
breadthFirstAlternatives xs = now ++ concatMap breadthFirstAlternatives later
  where (now,later) = unzip $ alternativesTree xs

alternateEveryOnce :: [[Int]] -> [[Int]]
alternateEveryOnce []            = []
alternateEveryOnce ((x:y:xs):ys) = (y:map head ys) : map (x:) (alternateEveryOnce ys)
alternateEveryOnce ([x]:ys)      = map (x:) $ alternateEveryOnce ys

vectorAlternatives :: [Int] -> [Subset] -> [[Int]]
vectorAlternatives = zipWith alternatives

optimize :: Integer -> [Int] -> [Subset] -> Maybe [Int]
optimize 0 x y = Just x
optimize diff [] []         = Nothing
optimize diff (s:ss) (x:xs) =
  if value nearest x == target
  then Just (nearest:ss)
  else fmap (s :) $ optimize diff ss xs
  where nearest = findNearest target x
        target = fromInteger (toInteger (value s x) + diff)

optimizeSize :: Int -> [Int] -> [Subset] -> Maybe [Int]
optimizeSize 0 x y = Just x
optimizeSize diff [] [] = Nothing
optimizeSize diff (s:ss) (x:xs) =
  fmap (bestAlternative :) $ optimizeSize (diff - delta bestAlternative) ss xs
  where orig = popCount s
        delta x = popCount x - orig
        bestAlternative = head $ sortOn (\x -> abs $ diff - delta x) (equalAlternatives s x)

naiveIterate :: Integer -> [Integer] -> Map.Map (Integer,Int) [Integer] -> Map.Map (Integer,Int) [Integer]
naiveIterate i xs map = foldl' (naiveInsert i) map $ zip xs (zip (tail xs ++ [0]) [1..])

naiveRanges :: [Integer] -> [Integer]
naiveRanges items = foldr (\(l,h) f _ -> [l..h] ++ f h) (\h -> [h..]) ranges 0
  where ranges = takeWhile (\(l,h) -> h-l <= min) $ iterate (\(l,h) -> (l+min,h+max)) (min,max)
        min = minimum items
        max = maximum items

naiveInsert :: Integer -> Map.Map (Integer,Int) [Integer] -> (Integer,(Integer,Int)) -> Map.Map (Integer,Int) [Integer]
naiveInsert i map (y,(x,j)) =
  if i >= y then Map.alter (<|> (fmap (y:) $ Map.lookup (i - y,j-1) map)) (i,j) as else as
    where as = maybe (map) (\xs -> Map.insert (i,j) xs map) (Map.lookup (i,j-1) map)

naiveSearch :: Integer -> [Integer] -> [[Integer]]
naiveSearch n xs
  | n < 0 = []
  | n == 0 = [[]]
  | otherwise = maybeToList $ Map.lookup (n,length xs) $ foldl (\map n -> naiveIterate n xs map) startMap (naiveRanges xs)
    where startMap = Map.fromList $ map (\(x,j) -> ((0,j),[])) (zip xs [0..])

optimizeInput :: Integer -> [Integer] -> (Integer,[Integer],[Integer] -> [Integer])
optimizeInput target items = if max - target < target then (max - target, items, (items \\)) else (target,takeWhile (<= target) $ dropWhile (<=0) $ items,id)
  where n = length items
        maxK = (1+) $ length $ takeWhile (target>) $ scanl1 (+) items
        minK = (1+) $ length $ takeWhile (target>) $ scanl1 (+) (reverse items)
        max = sum items

maxK target items = length $ takeWhile (target>=) $ scanl1 (+) items
minK target items = (1+) $ length $ takeWhile (target>) $ scanl1 (+) (reverse items)

sizeHints :: Integer -> [Integer] -> [Int]
sizeHints target items = alternate lower higher
    where lower = takeWhile (>=min) $ map (mid-) $ map (* ((max-min) `div` 6)) [0..]
          higher = takeWhile (<=max) $ map (mid+) $ map (* ((max-min) `div` 6)) [1..]
          mid = (min + (max - min) `div` 2)
          max = maxK target items
          min = minK target items

subsetSearch :: Integer -> [Integer] -> [[Integer]]
subsetSearch target items = if target >= 0 then map (flip vectorValues subsets) resultVectors else []
  where subsets = extractSubsets items
        starts = sortOn (\v -> abs (target - vectorValue v subsets)) $ startVector target subsets : map (startVectorBySize target subsets) (sizeHints target items)
        alternatives = weightedIterate $ map (\start -> start : (breadthFirstAlternatives $ vectorAlternatives start subsets)) starts
        resultVectors = mapMaybe (\ps -> optimize (toInteger target - toInteger (vectorValue ps subsets)) ps subsets) alternatives

includedSearch :: Integer -> [Integer] -> [[Integer]]
includedSearch target = map (:[]) . take 1 . filter (==target)

mutate :: RandomGen g => (g,Integer,[(Integer,Bool)]) -> (g,Integer,[(Integer,Bool)])
mutate (gen,0,items) = (gen,0,items)
mutate (gen,target,[]) = (gen,target,[])
mutate (gen,target,((i,included):is))
  | diff + target == 0 = (gen,0,(i,not included):is)
  | p > x              = let (gen',t',is') = mutate (ngen,target + diff,is) in (gen',t',(i,not included):is')
  | otherwise          = let (gen',t',is') = mutate (ngen,target,is) in (gen',t',(i,included):is')
    where diff = if included then i else -i
          effect = (abs target) - (abs (target + diff))
          p = (atan (fromIntegral effect)) :: Double
          (x,ngen) = randomR (-pi/2.0,pi/2.0) gen

randomMutateSearch :: Integer -> [Integer] -> [[Integer]]
randomMutateSearch target items = filter ((==target) . sum) $ map (\(_,_,z) -> map fst $ filter snd z) it
  where it = iterate mutate (gen,target,zip items (repeat False))
        gen = mkStdGen (length items)

solveProblem :: (Integer,[Integer]) -> IO (Maybe [Integer])
solveProblem (target,items) = do
  putStrLn $ "looking for subset with sum " ++ show target
  resultV <- newEmptyMVar
  forkIO $ let r = listToMaybe $ naiveSearch target items in seq r $ putMVar resultV (NaiveSearch,r)
  forkIO $ let r = listToMaybe (includedSearch target items) in when (isJust r) $ putMVar resultV (IncludedSearch,r)
  forkIO $ let r = listToMaybe $ subsetSearch target items in seq r $ putMVar resultV (SubsetSearch,r)
  forkIO $ let r = listToMaybe $ randomMutateSearch target items in seq r $ putMVar resultV (RandomMutate,r)
  (searchType,result) <- takeMVar resultV
  return result

readProblemFromFile :: FilePath -> IO (Integer,[Integer])
readProblemFromFile path = do
  content <- readFile path
  let ls = lines content
  when (length ls /= 2) $ die "invalid input format"
  let [t,is] = ls
  return (read t,sort (read is))

readProblem :: IO (Integer,[Integer])
readProblem = do
  target <- readLn
  unorderedItems <- readLn
  return (target, sort unorderedItems)

displaySolution :: Maybe [Integer] -> IO ()
displaySolution Nothing = putStrLn "no subset exists"
displaySolution (Just r) = putStrLn $ "found subset: " ++ show r

showBounds :: Maybe (Integer,[Integer]) -> IO (Maybe (Integer,[Integer]))
showBounds = maybe (return Nothing) (\p -> f p >> return (Just p)) where
  f (target,items) =
    let min = minK target items in
    let max = maxK target items in
    putStrLn $ "bounds: 0..[" ++ show min ++ ".." ++ show max ++ "].." ++ show (length items)

showAverage :: Maybe (Integer,[Integer]) -> IO (Maybe (Integer,[Integer]))
showAverage = maybe (return Nothing) (\p -> f p >> return (Just p)) where
  f (target,items) = putStrLn $ "average: " ++ show (sum items `div` (toInteger (length items)))

parseArgs :: [String] -> IO (Maybe (Integer,[Integer]))
parseArgs [] = readProblem >>= return . Just
parseArgs [path] = readProblemFromFile path >>= return . Just
parseArgs ("--show":"bounds":args) = parseArgs args >>= showBounds
parseArgs ("--show":"average":args) = parseArgs args >>= showAverage
parseArgs ("--dry":args) = parseArgs args >> return Nothing
parseArgs ("--items":items:"--target":target:args) = return (Just (read target, sort (read items)))
parseArgs ("--target":target:"--items":items:args) = return (Just (read target, sort (read items)))

data CNF = CNF Int [[(Bool,Int)]] deriving Show

cnf :: [[String]] -> CNF
cnf (["p","cnf",vars,_]:xs) = CNF (read vars) (map parse $ (map (map read) xs)) where
  parse [a,b,c,0] = [(a >= 0, abs a), (b >= 0, abs b), (c >= 0, abs c)]

readCNF :: FilePath -> IO CNF
readCNF path = do
  content <- readFile path
  let lineFilter [] = False
      lineFilter ("c":_) = False
      lineFilter _ = True
  let ls = takeWhile (/= ["%"]) $ filter lineFilter $ map words (lines content)
  return $ cnf ls

cnfToSubsetSum :: CNF -> (Integer,[Integer])
cnfToSubsetSum (CNF vars clauses) = (s,xy++vs)
  where s = (sum v1) + (sum $ map ((shiftL 4).(3*)) [0..n])
        vs = zipWith (+) v1 v2 ++ zipWith (+) v1 v3
        v1 = map ((shiftL 1).(3*n+).(3*)) [1..vars]
        v2 = map (\x -> sum $ zipWith shiftL (map (toInteger . popCount . elem (True,x)) clauses) (map (*3) [0..])) [1..vars]
        v3 = map (\x -> sum $ zipWith shiftL (map (toInteger . popCount . elem (False,x)) clauses) (map (*3) [0..])) [1..vars]
        n = length clauses - 1
        xy = concatMap (\x -> let y = shiftL 1 (3*x) in [y,2*y]) [0..n]

main :: IO ()
main = do
  problem <- (getArgs >>= parseArgs)
  maybe (return ()) (\p -> solveProblem p >>= displaySolution) problem