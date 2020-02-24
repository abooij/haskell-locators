#!/usr/bin/env stack
-- stack --resolver lts-14.17 script

import Control.Monad (foldM)
import Data.Ratio ((%), numerator, denominator)
import Data.List (find, findIndex)
import Data.Maybe (fromJust, catMaybes)
import Data.IORef
import Debug.Trace
import GHC.Real (Ratio((:%)))
import Unsafe.Coerce (unsafeCoerce)
import System.IO.Unsafe (unsafePerformIO)

-- `l q r = LocatesLeft s` means `q < s < x`, and ditto for `LocatesRight.
data Location = LocatesLeft Rational | LocatesRight Rational deriving (Show, Eq)
-- opposite :: Location -> Location
-- opposite LocatesLeft = LocatesRight
-- opposite LocatesRight = LocatesLeft

-- Type of reals equipped with locators.
--
-- Compared to the definition in UTT, we have dropped the data
-- specifying the real itself, keeping only the locator.  This is
-- justified because given only the output "bits" of a locator, we can
-- recover the corresponding subsets of the rationals, and
-- correspondingly phrase when data specifies a Dedekind cut, although
-- this requirement is not captured in our Haskell implementation.
--
-- The locator accepts two rationals `q` and `r` as input, where it is
-- a requirement that `q<r`, although this is not checked explicitly.
data RL = RL
  { rl_locates :: Rational -> Rational -> Location
  , rl_best_left :: IORef (Maybe Rational)
  , rl_best_right :: IORef (Maybe Rational)
  }
save :: Location -> IORef (Maybe Rational) -> IORef (Maybe Rational) -> IO Location
save loc@(LocatesLeft left) best_left _ = writeIORef best_left (Just left) >> return loc
save loc@(LocatesRight right) _ best_right = writeIORef best_right (Just right) >> return loc
locates :: RL -> Rational -> Rational -> Location
locates rl q r = unsafePerformIO $ do
  --print (q,r)
  maybe_best_left <- readIORef (rl_best_left rl)
  maybe_best_right <- readIORef (rl_best_right rl)
  return $ go maybe_best_left maybe_best_right
    where
      go :: Maybe Rational -> Maybe Rational -> Location
      go (Just s) _ | s < r = LocatesLeft s
      go _ (Just s) | q < s  = LocatesRight s
      go _ _ = unsafePerformIO $ save (rl_locates rl q r) (rl_best_left rl) (rl_best_right rl) -- todo: save result.

-- `locatesLeft l q r` is true when the real locates to the left of
-- `r`.  That is, if we think of `l` as representing a real `x`, then
-- `locatesLeft l q r -> (x < r)`.
locatesLeft :: RL -> Rational -> Rational -> Bool
locatesLeft rl q r = case locates rl q r of LocatesLeft _ -> True; _ -> False
locatesRight :: RL -> Rational -> Rational -> Bool
locatesRight rl q r = case locates rl q r of LocatesRight _ -> True; _ -> False

-- version that saves in IORefs.
pack_comp :: (Rational -> Rational -> Location) -> IO RL
pack_comp l = do
  left <- newIORef Nothing
  right <- newIORef Nothing
  return $ RL { rl_locates = l
              , rl_best_left = left
              , rl_best_right = right
              }

-- Version that doesn't save anything
pack_comp_pure :: (Rational -> Rational -> Location) -> RL
pack_comp_pure l = unsafePerformIO $ do
  left <- newIORef Nothing
  right <- newIORef Nothing
  return $ RL { rl_locates = l
              , rl_best_left = left
              , rl_best_right = right
              }

-- Construct a real with a locator for a given rational number `s`.
mkRat = mkRat_ii

-- optimistically assume that the denominator is positive (probably not true with the algebraic operations below)
{-
mkRat_i :: Rational -> RL
mkRat_i s@(x:%y) q r =
  let
    prev = ((x-1):%y)
    next = ((x+1):%y)
    go
         | q < prev  = LocatesRight prev
         | next < r  = LocatesLeft  next
         | q < s     = LocatesRight q
         | otherwise = LocatesLeft  r
  in go -- (s, q, r) `traceShow` go
-}

mkRat_ii :: Rational -> IO RL
mkRat_ii s = pack_comp l
  where
    l :: Rational -> Rational -> Location
    l q r | s < r     = LocatesLeft r
          | otherwise = LocatesRight q

-- Debugging variant of `mkRat` which outputs a given text every time it's invoked.
{-
mkRat' :: Rational -> String -> RL
mkRat' s str q r = (str,q,r) `traceShow` mkRat s q r
-}

-- Given a real with a locator, compute a lower bound for it.
lowerBound = lowerBound_iv

-- Try only exponentials.
lowerBound_ii :: RL -> Rational
lowerBound_ii l = fromJust $ find go qs
  where
    go :: Rational -> Bool
    go q = locatesRight l (q - 1) q
    qs :: [Rational]
    qs = map (fromInteger . (0-) . (2^)) [0..]
-- Variant in which we take powers later, which doesn't seem to make a difference (as expected).
lowerBound_iii :: RL -> Rational
lowerBound_iii l = fromInteger $ (\n-> -(2^n)) $ fromJust $ out
  where
    go :: Integer -> Bool
    go n = let p = -(2^n) in locatesRight l (fromInteger (p)) (fromInteger (p+1))
    qs :: [Integer]
    qs = [0..]
    out = find go qs

lowerBound_iv :: RL -> Rational
lowerBound_iv l = go (-2) (-1)
  where
    go :: Rational -> Rational -> Rational
    go q r =
      case locates l q r of
        LocatesLeft s ->
          let n = min s r
          in -- (if n < r then "GO GO GO down" else ("NO NO NO down " ++ show (s,r)) ) `trace`
          go (4*n) (2*n)
        LocatesRight t ->
          -- ("lower done ", t) `traceShow`
          t

-- Upper bounds, c.f. `lowerBound`.
upperBound = upperBound_iv

upperBound_iv :: RL -> Rational
upperBound_iv l = go 1 2
  where
    go :: Rational -> Rational -> Rational
    go q r =
      case locates l q r of
        LocatesRight s ->
          let n = max s q
          in --(if n > q then "GO GO GO up" else ("NO NO NO up " ++ show (s,q)) ) `trace`
          go (2*n) (4*n)
        LocatesLeft  t ->
          -- ("upper done ", t) `traceShow`
          t

-- One-dimensional version of Sperner's lemma: given a finite list of
-- elements, with the first element not satisfying some predicate `f`,
-- and the last satisfying it, there is some index `i` where element
-- `i` doesn't satisfy the predicate, and `i+1` does.
--
-- Note that this encoding of Sperner's lemma is radically
-- insufficient for our development as it requires the construction of
-- the entire input list `xs`.  A more efficient variant, `sperner'`,
-- rather does a bisection-style algorithm which does not require
-- keeping the entire list of elements in memory.
sperner = sperner_ii

-- smarter bisection-style algorithm, still suffering from needing the
-- entire list in memory.
sperner_ii :: (a -> Bool) -> [a] -> Int
sperner_ii f xs = go 0 (length xs - 1)
  where
    go :: Int -> Int -> Int
    go left right
      | right == left + 1 = left
      | f (xs !! ((left + right) `div` 2)) == False = go ((left + right) `div` 2) right
      | otherwise                                   = go left ((left + right) `div` 2)

-- Output the "Sperner element" (c.f. `sperner`) rather than its index.
spernerFind :: (a -> Bool) -> [a] -> a
spernerFind f xs =
  let i = sperner f xs
  in (xs !! i)

-- Application of Sperner's lemma to locators.
spernerLocate :: RL -> [Rational] -> Int
spernerLocate l qs = sperner (\(q, r) -> locatesLeft l q r) (zip (init qs) (tail qs))

-- Output rationals rather than an index, c.f. `spernerFind`
spernerLocateFind :: RL -> [Rational] -> (Rational, Rational)
spernerLocateFind l qs =
  let i = spernerLocate l qs
  in (qs !! i , qs !! (i+2))

-- Fix of the encoding problem with `sperner`: given a predicate about
-- a finite collection, and a start and end point, find a point where
-- the predicate switches from false to true, without needing to have
-- a list in memory.
sperner' :: (Integer -> Bool) -> Integer -> Integer -> Integer
sperner' f start end = go start end
  where
    go :: Integer -> Integer -> Integer
    go left right =
      let mid = ((left + right) `div` 2)
          x | right == left + 1 = left
            | f mid == False = go mid right
            | otherwise      = go left mid
      in x

spernerLocate' :: RL -> (Integer -> Rational) -> Integer -> Integer -> Integer
spernerLocate' l f start end =
  sperner' (\i -> locatesLeft l (f i) (f (i + 1))) start end

spernerLocateFind' :: RL -> (Integer -> Rational) -> Integer -> Integer -> (Rational, Rational)
spernerLocateFind' l f start end =
  let i = spernerLocate' l f start end
  in (f (fromIntegral i) , f (fromIntegral i+2))

-- Given a real x with a locator `l`, and a positive error bound
-- `epsilon`, find rationals `(u, v)` with `u<x<v` and `v-u<epsilon`
tightBound = tightBound_ii

tightBound_i :: RL -> Rational -> (Rational, Rational)
tightBound_i l epsilon =
  let q = lowerBound l
      r = upperBound l
      n :: Integer
      n = ceiling (3*(r-q)/epsilon)
      start :: Rational
      start = q - epsilon/3
      end :: Rational
      end = q + (fromInteger n+1) * epsilon / 3
      qs = [start, q .. end]
  in
    spernerLocateFind l qs

infixl 6 +:+
infixl 7 *:*
-- Compute with rationals without reducing the rational.
(+:+) :: Rational -> Rational -> Rational
(x:%y) +:+ (x':%y') = (x*y' + x'*y) :% (y*y')
(*:*) :: Rational -> Rational -> Rational
(x:%y) *:* (x':%y') = (x * x') :% (y * y')
(-:-) :: Rational -> Rational -> Rational
(x:%y) -:- (x':%y') = (x*y' - x'*y) :% (y*y')
(/:/) :: Rational -> Rational -> Rational
(x:%y) /:/ (x':%y') = (x * y') :% (y * x')

-- compute rationals without reducing because comparison is
-- reduction-independent
tightBound_ii :: RL -> Rational -> (Rational, Rational)
tightBound_ii l epsilon =
  let q = lowerBound l
      r = upperBound l
      n :: Integer
      n = ceiling (3*:*(r-:-q)/:/epsilon)
      qs = [-1..(n+1)]
      e = epsilon /:/ 3
      f :: Integer -> Rational
      f i = q +:+ fromInteger i *:* e
  in
    spernerLocateFind' l f (-1) (n+1)

-- Given a locator for a real `x`, construct a locator for `-x`.
mkMinus :: RL -> RL
mkMinus l = pack_comp_pure go
  where
  go q r = case locates l (-r) (-q) of
    LocatesLeft  s -> LocatesRight (-s)
    LocatesRight s -> LocatesLeft  (-s)

-- Given locators for `x` and `y`, construct a locator for `x+y`.
mkPlus :: RL -> RL -> IO RL
mkPlus l m = pack_comp go
  where
    go q r =
      let epsilon = (r -:- q) /:/ 2
          (u, v) = tightBound l epsilon
          s = q -:- u
      in --("plus", (u,v), s, epsilon, m s (s +:+ epsilon)) `traceShow`
        case locates m s (s +:+ epsilon) of
          LocatesLeft t -> LocatesLeft (v+t)
          LocatesRight t -> LocatesRight (u+t)

-- Given a locator for a real `x` and a rational `s`, construct a
-- locator for `x+s`.
--
-- This specialization of `mkPlus` is vastly more efficient as it
-- avoids calling `tightBound`.
mkPlusRat :: RL -> Rational -> RL
mkPlusRat l s = pack_comp_pure go
  where
    go q r = locates l (q-:-s) (r-:-s)

-- Construct a locator for `min(x,y)`
mkMin :: RL -> RL -> RL
mkMin l m = pack_comp_pure go
  where
    go q r = case (locates l q r, locates m q r) of
      (LocatesRight s, LocatesRight t) -> LocatesRight (min s t)
      (LocatesRight s, LocatesLeft  t) -> LocatesLeft  t
      (LocatesLeft  s, LocatesRight t) -> LocatesLeft  s
      (LocatesLeft  s, LocatesLeft  t) -> LocatesLeft  (max s t)

-- Construct a locator for `max(x,y)`.
mkMax :: RL -> RL -> RL
mkMax l m = pack_comp_pure go
  where
    go q r = case (locates l q r, locates m q r) of
      (LocatesRight s, LocatesRight t) -> LocatesRight (min s t)
      (LocatesRight s, LocatesLeft  t) -> LocatesRight s
      (LocatesLeft  s, LocatesRight t) -> LocatesRight t
      (LocatesLeft  s, LocatesLeft  t) -> LocatesLeft  (max s t)

-- Given a locator for `x`, construct a locator for the absolute value
-- `|x|`
mkAbs :: RL -> RL
mkAbs l = mkMax l (mkMinus l)

-- Construct a locator for the product `x*y`.
mkTimes = mkTimes_iii

-- Approximate l and m to cross-wise precision.
-- NB these computations have not been checked. Are the error bounds OK?
mkTimes_iii :: RL -> RL -> IO RL
mkTimes_iii l m = pack_comp go
  where
    go q r =
      let xmax = mkPlusRat (mkAbs l) 1
          z = upperBound xmax
          ymax = mkPlusRat (mkAbs m) 1
          w = upperBound ymax
          epsilon = r -:- q
          delta = min 1 (epsilon /:/ (2 *:* z))
          eta   = min 1 (epsilon /:/ (2 *:* w))
          (a, b) = tightBound l eta
          (c, d) = tightBound m delta
          fourmin = min (min (a*:*c) (a*:*d)) (min (b*:*c) (b*:*d))
          fourmax = max (max (a*:*c) (a*:*d)) (max (b*:*c) (b*:*d))
          out = case q < fourmin of
            True -> LocatesRight fourmin
            _    -> LocatesLeft fourmax
      in out

-- Two constructions stolen from stackexchange
-- https://stackoverflow.com/questions/20516402/cartesian-product-of-infinite-lists-haskell
kart_i3 xs ys = g [] [map (\y -> (x,y)) ys | x <- xs]
  where                                          -- works both for finite
     g [] [] = []                                --  and infinite lists
     g a  b  = concatMap (take 1) a
                ++ g (filter (not.null) (take 1 b ++ map (drop 1) a))
                     (drop 1 b)
-- https://stackoverflow.com/questions/9749904/what-is-a-good-way-to-generate-a-infinite-list-of-all-integers-in-haskell
integers :: [Integer]
integers = 0 : [y | x <- [1..], y <- [x,-x]]
-- Enumerate pairs of positive naturals
enum_NN :: [(Integer, Integer)]
enum_NN = kart_i3 [1..] [1..]
-- Enumerate pairs of integers with positive naturals
enum_ZN :: [(Integer, Integer)]
enum_ZN = kart_i3 integers [1..]
-- enumerate POSITIVE rationals
enum_Qpos :: [Rational]
enum_Qpos = map (uncurry (%)) enum_NN
-- enumerate ALl rationals
enum_Q :: [Rational]
enum_Q = map (uncurry (%)) enum_ZN
-- enumerate pairs of rationals with positive rationals
enum_QQpos :: [(Rational, Rational)]
enum_QQpos = kart_i3 enum_Q enum_Qpos

-- Given two reals `x` and `y` with locators, find a rational `x<q<y`
-- in between them
archStruct = archStruct_ii

archStruct_i :: RL -> RL -> Rational
archStruct_i l m =
  let (q , epsilon) = fromJust $ find (\ p@(q , epsilon) -> locatesLeft l (q - epsilon) q && locatesRight m q (q + epsilon)) enum_QQpos
  in q

-- enumerate all rationals, with ever decreasing errors
enum_QQpos' :: [(Rational, Rational)]
enum_QQpos' = zip enum_Q $ map (1%) [1..]

-- skip some useless searches that *increase* epsilon
archStruct_ii :: RL -> RL -> Rational
archStruct_ii l m =
  let (q , epsilon) = fromJust $ find (\ p@(q , epsilon) -> locatesLeft l (q - epsilon) q && locatesRight m q (q + epsilon)) enum_QQpos'
  in q

data Side = FirstLocatesLeft | SecondLocatesRight
-- A kind of cotransitivity of reals with locators: if `x<y` then
-- either `x<s` or `s<y`.  In fact, this also holds for a real `z`
-- with a locator, but we do not need this.
cotrans :: RL -> RL -> Rational -> Side
cotrans l m s =
  let q = archStruct l m
  in case q <= s of
    True -> FirstLocatesLeft
    _    -> SecondLocatesRight

{-
-- Given a positive real with a locator, compute a locator for its
-- multiplicative inverse.
mkReciprocalPos = mkReciprocalPos_ii

-- getting (q < x^-1) + (x^-1 < r) is equivalent to
--         (qx < 1)   + (1    < rx), *NOT* equivalent to
--         (x  < 1/q) + (1/r  <  x)
-- but wlog 0<q (o/w q<=0<x so q<x)
-- and so  equiv:  (x < 1/q) + (1/r < x)
-- i.e. (1/r < x) + (x < 1/q)
mkReciprocalPos_ii :: RL -> RL
mkReciprocalPos_ii l q r
  | q <= 0    = LocatesRight 0
  | otherwise =
    case l (1/r) (1/q) of
      LocatesLeft  s -> LocatesRight (1/s)
      LocatesRight s -> LocatesLeft  (1/s)

-- Given a negative real with a locator, compute a locator for its
-- multiplicative inverse.
mkReciprocalNeg = mkReciprocalNeg_ii

-- getting (q < x^-1) + (x^-1 < r) is equivalent to
--         (1 <  qx ) + (rx   < 1), *NOT* equivalent to
--         (1/q < x)  + (x    < 1/r)
-- but wlog r<0 (o/w 0 <= 1/r so x < 0 <= 1/r, so rx < 1, so x^-1 < r)
-- and so  equiv:  (x < 1/q) + (1/r < x)
-- i.e. (1/r < x) + (x < 1/q), which can be decided because q<r<0 i.e. 1/r < 1/q
mkReciprocalNeg_ii :: RL -> RL
mkReciprocalNeg_ii l q r
  | 0 <= r    = LocatesLeft 0
  | otherwise =
    case l (1/r) (1/q) of
      LocatesLeft  s -> LocatesRight (1/s)
      LocatesRight s -> LocatesLeft  (1/s)

data Sign = Positive | Negative deriving (Show, Eq)
-- In UTT, given `x#0` (`x` is apart from 0), it is decidable if
-- `0<x`.  However, since we do not represent inequalities in this
-- development, we need to compute the sign of `x` explicitly, which
-- we do using the locator.
decideSign :: RL -> Sign
decideSign l = head $ catMaybes $ map go (tail integers)
  where
    go :: Integer -> Maybe Sign
    go n | n > 0 = if locatesRight l 0 (1 % n) then Just Positive else Nothing
         | n < 0 = if locatesLeft l (1 % n) 0 then Just Negative else Nothing
         | otherwise = Nothing

-- Having first computed the sign of `x`, where `x#0`, we can compute
-- its reciprocal.
mkReciprocal :: RL -> RL
mkReciprocal l =
  case decideSign l of
    Positive -> mkReciprocalPos l
    Negative -> mkReciprocalNeg l

-- Given a regular sequence of locators, compute a locator for its limit
-- Here, regular means |x_m-x_n|<(1/m)+(1/n)
mkLimit :: (Integer -> RL) -> RL
mkLimit ls q r =
  let epsilon = (r - q) / 3
  in ls (ceiling (1 / epsilon)) (q + epsilon) (r - epsilon) -- just made a guess w.r.t the error bound here -- TODO fix output rational
-}

intBound :: RL -> Integer
intBound l =
  let (u, v) = tightBound l 1
  in (floor u) + 1

-- Signed-digit representaion.
sdr :: RL -> (Integer, [Int])
sdr l = (k, tail ds) where
  k :: Integer
  k = intBound l
  intermediateSum :: [Int] -> Rational
  intermediateSum as = (fromInteger k +) $ sum $ map (\(a, i) -> (fromIntegral a) * 10^^(-i)) $ zip as ([1..] :: [Integer])

  -- Intermediate sum, current precision
  mkDigit :: Rational -> Integer -> Int
  mkDigit s i =
    let j = spernerLocate l [s-10^^(-i), s-9*10^^(-i-1) .. s+10^^(-i)]
    in  j-9
  f :: (Rational, Integer, Int) -> (Rational, Integer, Int)
  f t@(s, i, _) =
    let d = mkDigit s i
    in (s + (fromIntegral d) * 10^^(-i-1), i+1, d)
  go :: [(Rational, Integer, Int)]
  go = iterate f (fromIntegral k, 0, 0)
  ds :: [Int]
  (_, _, ds) = unzip3 go

-- Initial segment of the signed-digit representation
sdrFinite :: RL -> Int -> (Integer, [Int])
sdrFinite l n =
  let (k, ds) = sdr l
  in (k, take n ds)
{-
main = do
  let q1 = mkRat 1
      q100 = mkRat 100
      q5 = mkRat 5
      q = mkRat
      q' x = mkMinus (mkRat (-x))
  print $ q1 0 2
  print "lowerBound"
  print $ lowerBound q1
  print $ lowerBound (mkMinus q1)
  print $ lowerBound (mkRat (-1.5))
  print "upperBound"
  print $ upperBound q1
  print $ upperBound (mkRat (-1.5))
  print "tightBound"
  print $ tightBound q1 (1/3)
  print $ tightBound (mkRat 200) (5)
  print $ tightBound (mkRat 200) (1/5)
  print $ tightBound (mkPlus q1 q1) (1/2)
  print $ tightBound (mkMin q1 q100) (1/2)
  print "archStruct"
  print $ archStruct q1 q100
  print $ archStruct (mkRat 10) q100
  print $ archStruct (mkMinus q100) q100
  print "upper/lowerBound algebra"
  print $ upperBound (mkTimes q5 (q 4))
  print $ upperBound (q (1.5))
  print $ upperBound (mkMinus (q (-1.5)))
  print $ decideSign (q (-0.1))
  print $ upperBound (mkReciprocal (q 1))
  print $ lowerBound (mkReciprocal (q 1))
  print $ lowerBound (mkReciprocal (q (-1/100)))
  print $ upperBound (mkPlus (q 2) (mkReciprocal (q (-3))))
  -- print $ upperBound (foldr1 mkPlus (replicate 14 (q (3))))
  print "tightBound limit"
  let ls i = q (2 - 1 / (fromInteger i))
  print $ tightBound (mkLimit ls) 1
  print "intBound"
  print $ intBound (q 100.5)
  print "sdr"
  let q2 _ = mkRat 20 -- let q2 = mkRat' 2
  --print $ sdrFinite (mkPlus (q2 "a") (mkPlus (q2 "b") (mkPlus (q2 "c") (mkPlus (q2 "d") (mkPlus (q2 "e") (mkPlus (q2 "f") (mkPlus (q2 "g") (mkPlus (q2 "h") (q2 "i"))))))))) 5
  print $ sdrFinite (mkTimes (q2 "a") (mkTimes (q2 "b") (mkTimes (q2 "c") (q2 "d")))) 5
  -- let q2' = mkRat' 2
  -- print $ tightBound (mkTimes (q2' "a") (mkPlus (q2' "b") (q2' "c"))) (1/100000000)
  print $ sdrFinite (q (1/3)) 10
  print $ sdrFinite (q (1/7)) 10
  print $ sdrFinite (q' (1/7)) 10
  print $ sdrFinite (mkLimit ls) 10
  print $ sdrFinite (mkPlus (q 20) (q 0.5)) 2
  print $ sdrFinite (q 16) 2
  print $ sdrFinite (foldr1 mkPlus (replicate 10 (q (-2)))) 5
  print $ sdrFinite (foldr1 mkTimes (replicate 4 (q (-20)))) 5
  print $ sdrFinite (mkTimes (q 0.00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002) (q 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) 2

main''' = print $ upperBound (mkTimes (mkRat' (-2) "a") (mkTimes (mkRat' (-2) "b") (mkTimes (mkRat' (-2) "c") (mkTimes (mkRat' (-2) "d") (mkRat' (-2) "e")))))
main'' = print $ upperBound (foldr1 mkTimes (replicate 5 (mkRat (-2))))
main' = do
  print "lowerBound"
  print $ lowerBound (mkPlus (mkRat' 1000 "a") (mkRat' (-(1000)) "b"))
  print "upperBound"
  print $ upperBound (mkPlus (mkRat' (1000) "a") (mkRat' (-1000) "b"))
  print "big sum"
  print $ upperBound (foldr1 mkPlus (replicate 10 (mkRat (-20000))))
  print $ sdrFinite (foldr1 mkPlus (replicate 10 (mkRat (-20000)))) 5
-}
main = do
  q2 <- mkRat (-2)
  q20 <- mkRat (-20)
  plus <- foldM mkPlus q2 (replicate 10 q2)
  print $ sdrFinite plus 5
--  times <- foldM mkTimes q20 (replicate 3 q20)
--  print $ sdrFinite times 5
