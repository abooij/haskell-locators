#!/usr/bin/env stack
-- stack --resolver lts-14.17 script

import Data.Ratio ((%), numerator, denominator)
import Data.List (find, findIndex)
import Data.Maybe (fromJust, catMaybes)
import Debug.Trace
import GHC.Real (Ratio((:%)))
import Unsafe.Coerce (unsafeCoerce)

data Location = LocatesLeft | LocatesRight deriving (Show, Eq)
opposite :: Location -> Location
opposite LocatesLeft = LocatesRight
opposite LocatesRight = LocatesLeft

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
type Locator = Rational -> Rational -> Location
-- `locatesLeft l q r` is true when the real locates to the left of
-- `r`.  That is, if we think of `l` as representing a real `x`, then
-- `locatesLeft l q r -> (x < r)`.
locatesLeft :: Locator -> Rational -> Rational -> Bool
locatesLeft l q r = l q r == LocatesLeft
locatesRight :: Locator -> Rational -> Rational -> Bool
locatesRight l q r = l q r == LocatesRight

-- Construct a real with a locator for a given rational number `s`.
mkRat = mkRat_i

mkRat_i :: Rational -> Locator
mkRat_i s q r
  | q < s = LocatesRight
  | otherwise = LocatesLeft

mkRat_ii :: Rational -> Locator
mkRat_ii s q r
  | s < r = LocatesLeft
  | otherwise = LocatesRight

-- Debugging variant of `mkRat` which outputs a given text every time it's invoked.
mkRat' :: Rational -> String -> Locator
mkRat' s str q r = str `trace` mkRat s q r

-- Given a real with a locator, compute a lower bound for it.
lowerBound = lowerBound_ii

lowerBound_i :: Locator -> Rational
lowerBound_i l = head [fromInteger (q-1)|q<-[0,-1..], l (fromInteger (q-1)) (fromInteger q) == LocatesRight]

-- Try only exponentials.
lowerBound_ii :: Locator -> Rational
lowerBound_ii l = fromJust $ find go qs
  where
    go :: Rational -> Bool
    go q = locatesRight l (q - 1) q
    qs :: [Rational]
    qs = map (fromInteger . (0-) . (2^)) [0..]
-- Variant in which we take powers later, which doesn't seem to make a difference (as expected).
lowerBound_iii :: Locator -> Rational
lowerBound_iii l = fromInteger $ (\n-> -(2^n)) $ fromJust $ out
  where
    go :: Integer -> Bool
    go n = let p = -(2^n) in locatesRight l (fromInteger (p)) (fromInteger (p+1))
    qs :: [Integer]
    qs = [0..]
    out = find go qs

-- Upper bounds, c.f. `lowerBound`.
upperBound = upperBound_ii

upperBound_i :: Locator -> Rational
upperBound_i l = head [fromInteger (q+1)|q<-[0..], l (fromInteger q) (fromInteger (q+1)) == LocatesLeft]
upperBound_ii :: Locator -> Rational
upperBound_ii l = fromJust $ find go qs
  where
    go :: Rational -> Bool
    go q = locatesLeft l q (q + 1)
    qs :: [Rational]
    qs = map (fromInteger . (2^)) [0..]
upperBound_iii :: Locator -> Rational
upperBound_iii l = fromInteger $ (\n-> (2^n)) $ fromJust $ find go qs
  where
    go :: Integer -> Bool
    go n = let p = 2^n in locatesLeft l (fromInteger (p-1)) (fromInteger (p))
    qs :: [Integer]
    qs = [0..]

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

sperner_i :: (a -> Bool) -> [a] -> Int
sperner_i f xs =
  let pairs = zip (init xs) (tail xs)
      i = fromJust $ findIndex (\(a, b) -> not (f a) && f b) pairs
  in i

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
spernerLocate :: Locator -> [Rational] -> Int
spernerLocate l qs = sperner (\(q, r) -> locatesLeft l q r) (zip (init qs) (tail qs))

-- Output rationals rather than an index, c.f. `spernerFind`
spernerLocateFind :: Locator -> [Rational] -> (Rational, Rational)
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

spernerLocate' :: Locator -> (Integer -> Rational) -> Integer -> Integer -> Integer
spernerLocate' l f start end =
  sperner' (\i -> locatesLeft l (f i) (f (i + 1))) start end

spernerLocateFind' :: Locator -> (Integer -> Rational) -> Integer -> Integer -> (Rational, Rational)
spernerLocateFind' l f start end =
  let i = spernerLocate' l f start end
  in (f (fromIntegral i) , f (fromIntegral i+2))

-- Given a real x with a locator `l`, and a positive error bound
-- `epsilon`, find rationals `(u, v)` with `u<x<v` and `v-u<epsilon`
tightBound = tightBound_ii

tightBound_i :: Locator -> Rational -> (Rational, Rational)
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

e = mkLimit (\n -> mkRat ((1+1%n) ^ (fromIntegral n)))

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
tightBound_ii :: Locator -> Rational -> (Rational, Rational)
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
mkMinus :: Locator -> Locator
mkMinus l q r = opposite $ l (-r) (-q)

-- Given locators for `x` and `y`, construct a locator for `x+y`.
mkPlus :: Locator -> Locator -> Locator
mkPlus l m q r =
  let epsilon = (r -:- q) /:/ 2
      (u, _) = tightBound l epsilon
      s = q -:- u
  in m s (s +:+ epsilon)

-- Given a locator for a real `x` and a rational `s`, construct a
-- locator for `x+s`.
--
-- This specialization of `mkPlus` is vastly more efficient as it
-- avoids calling `tightBound`.
mkPlusRat :: Locator -> Rational -> Locator
mkPlusRat l s q r = l (q-:-s) (r-:-s)

-- Construct a locator for `min(x,y)`
mkMin :: Locator -> Locator -> Locator
mkMin l m q r =
  case (l q r, m q r) of
    (LocatesRight, LocatesRight) -> LocatesRight
    _ -> LocatesLeft

-- Construct a locator for `max(x,y)`.
mkMax = mkMax_i -- seemingly no performance difference (as expected
                -- because the Core probably looks the same)

mkMax_i :: Locator -> Locator -> Locator
mkMax_i l m q r =
  case (l q r, m q r) of
    (LocatesLeft, LocatesLeft) -> LocatesLeft
    _ -> LocatesRight

mkMax_ii :: Locator -> Locator -> Locator
mkMax_ii l m q r =
  case (l q r) of
    LocatesLeft -> case m q r of
      LocatesLeft -> LocatesLeft
      _ -> LocatesRight
    _ -> LocatesRight

-- Given a locator for `x`, construct a locator for the absolute value
-- `|x|`
mkAbs :: Locator -> Locator
mkAbs l = mkMax l (mkMinus l)

-- Construct a locator for the product `x*y`.
mkTimes = mkTimes_iii

mkTimes_i :: Locator -> Locator -> Locator
mkTimes_i l m q r =
  let bimax = mkPlus (mkMax (mkAbs l) (mkAbs m)) (mkRat 1)
      z = upperBound bimax
      epsilon = r - q
      delta = min 1 (epsilon / (2 * z))
      (a, b) = tightBound l delta
      (c, d) = tightBound m delta
      mn = min (min (a*:*c) (a*:*d)) (min (b*:*c) (b*:*d))
      out = case q < mn of
        True -> LocatesRight
        _    -> LocatesLeft
  in out

-- The implementation of mkTimes, and in particular the usage of
-- `tightBound` on `l` and `m`, is the current bottleneck in this
-- development.  A possible problem is that, for small `l` and large
-- `m`, we approximate `m` to the same precision as we do `l`.
-- However, this is not needed: because of the smallness of `l`, it
-- suffices to approximate `m` badly.
mkTimes_ii :: Locator -> Locator -> Locator
mkTimes_ii l m q r =
  let bimax = mkPlusRat (mkMax (mkAbs l) (mkAbs m)) 1
      z = upperBound bimax
      epsilon = r -:- q
      delta = min 1 (epsilon /:/ (2 *:* z))
      (a, b) = tightBound l delta
      (c, d) = tightBound m delta
      mn = -- (q,r,z,delta,a,b,c,d) `traceShow`
        min (min (a*:*c) (a*:*d)) (min (b*:*c) (b*:*d))
      out = case q < mn of
        True -> LocatesRight
        _    -> LocatesLeft
  in out

-- Approximate l and m to cross-wise precision.
-- NB these computations have not been checked. Are the error bounds OK?
mkTimes_iii :: Locator -> Locator -> Locator
mkTimes_iii l m q r =
  let xmax = mkPlusRat (mkAbs l) 1
      z = upperBound xmax
      ymax = mkPlusRat (mkAbs m) 1
      w = upperBound ymax
      epsilon = r -:- q
      delta = min 1 (epsilon /:/ (2 *:* z))
      eta   = min 1 (epsilon /:/ (2 *:* w))
      (a, b) = tightBound l eta
      (c, d) = tightBound m delta
      mn = -- (q,r,z,delta,w,eta,a,b,c,d) `traceShow`
        min (min (a*:*c) (a*:*d)) (min (b*:*c) (b*:*d))
      out = case q < mn of
        True -> LocatesRight
        _    -> LocatesLeft
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

archStruct_i :: Locator -> Locator -> Rational
archStruct_i l m =
  let (q , epsilon) = fromJust $ find (\ p@(q , epsilon) -> l (q - epsilon) q == LocatesLeft && m q (q + epsilon) == LocatesRight) enum_QQpos
  in q

-- enumerate all rationals, with ever decreasing errors
enum_QQpos' :: [(Rational, Rational)]
enum_QQpos' = zip enum_Q $ map (1%) [1..]

-- skip some useless searches that *increase* epsilon
archStruct_ii :: Locator -> Locator -> Rational
archStruct_ii l m =
  let (q , epsilon) = fromJust $ find (\ p@(q , epsilon) -> l (q - epsilon) q == LocatesLeft && m q (q + epsilon) == LocatesRight) enum_QQpos'
  in q

data Side = FirstLocatesLeft | SecondLocatesRight
-- A kind of cotransitivity of reals with locators: if `x<y` then
-- either `x<s` or `s<y`.  In fact, this also holds for a real `z`
-- with a locator, but we do not need this.
cotrans :: Locator -> Locator -> Rational -> Side
cotrans l m s =
  let q = archStruct l m
  in case q <= s of
    True -> FirstLocatesLeft
    _    -> SecondLocatesRight

-- Given a positive real with a locator, compute a locator for its
-- multiplicative inverse.
mkReciprocalPos = mkReciprocalPos_ii

mkReciprocalPos_i :: Locator -> Locator
mkReciprocalPos_i l q r =
  let qx = mkTimes (mkRat q) l
      rx = mkTimes (mkRat r) l
  in case cotrans qx rx 1 of
    FirstLocatesLeft -> LocatesRight
    SecondLocatesRight -> LocatesLeft

-- getting (q < x^-1) + (x^-1 < r) is equivalent to
--         (qx < 1)   + (1    < rx), *NOT* equivalent to
--         (x  < 1/q) + (1/r  <  x)
-- but wlog 0<q (o/w q<=0<x so q<x)
-- and so  equiv:  (x < 1/q) + (1/r < x)
-- i.e. (1/r < x) + (x < 1/q)
mkReciprocalPos_ii :: Locator -> Locator
mkReciprocalPos_ii l q r
  | q <= 0    = LocatesRight
  | otherwise = opposite $ l (1/r) (1/q)

-- Given a negative real with a locator, compute a locator for its
-- multiplicative inverse.
mkReciprocalNeg = mkReciprocalNeg_ii

mkReciprocalNeg_i :: Locator -> Locator
mkReciprocalNeg_i l q r =
  let qx = mkTimes (mkRat q) l
      rx = mkTimes (mkRat r) l
  in case cotrans rx qx 1 of
    FirstLocatesLeft -> LocatesLeft
    SecondLocatesRight -> LocatesRight

-- getting (q < x^-1) + (x^-1 < r) is equivalent to
--         (1 <  qx ) + (rx   < 1), *NOT* equivalent to
--         (1/q < x)  + (x    < 1/r)
-- but wlog r<0 (o/w 0 <= 1/r so x < 0 <= 1/r, so rx < 1, so x^-1 < r)
-- and so  equiv:  (x < 1/q) + (1/r < x)
-- i.e. (1/r < x) + (x < 1/q), which can be decided because q<r<0 i.e. 1/r < 1/q
mkReciprocalNeg_ii :: Locator -> Locator
mkReciprocalNeg_ii l q r
  | 0 <= r    = LocatesLeft
  | otherwise = opposite $ l (1/r) (1/q)

data Sign = Positive | Negative deriving (Show, Eq)
-- In UTT, given `x#0` (`x` is apart from 0), it is decidable if
-- `0<x`.  However, since we do not represent inequalities in this
-- development, we need to compute the sign of `x` explicitly, which
-- we do using the locator.
decideSign :: Locator -> Sign
decideSign l = head $ catMaybes $ map go (tail integers)
  where
    go :: Integer -> Maybe Sign
    go n | n > 0 = if locatesRight l 0 (1 % n) then Just Positive else Nothing
         | n < 0 = if locatesLeft l (1 % n) 0 then Just Negative else Nothing
         | otherwise = Nothing

-- Having first computed the sign of `x`, where `x#0`, we can compute
-- its reciprocal.
mkReciprocal :: Locator -> Locator
mkReciprocal l =
  case decideSign l of
    Positive -> mkReciprocalPos l
    Negative -> mkReciprocalNeg l

-- Given a regular sequence of locators, compute a locator for its limit
-- Here, regular means |x_m-x_n|<(1/m)+(1/n)
mkLimit :: (Integer -> Locator) -> Locator
mkLimit ls q r =
  let epsilon = (r - q) / 3
  in ls (ceiling (1 / epsilon)) (q + epsilon) (r - epsilon) -- just made a guess w.r.t the error bound here

intBound :: Locator -> Integer
intBound l =
  let (u, v) = tightBound l 1
  in (floor u) + 1

-- Signed-digit representaion.
sdr :: Locator -> (Integer, [Int])
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
sdrFinite :: Locator -> Int -> (Integer, [Int])
sdrFinite l n =
  let (k, ds) = sdr l
  in (k, take n ds)

sdrDouble :: Locator -> Int -> Double
sdrDouble l n =
  let (k, ds) = sdrFinite l n
      vs = map (\(d, p) -> fromIntegral d * 10 ** (-p)) $ zip ds [1..]
      x :: Double
      x = fromIntegral k + sum vs
   in x

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
  let q2 = mkRat 2
  print $ sdrFinite (mkTimes q2 (mkTimes q2 (mkTimes q2 q2))) 5
  print $ sdrFinite (q (1/3)) 10
  print $ sdrFinite (q (1/7)) 10
  print $ sdrFinite (q' (1/7)) 10
  print $ sdrFinite (mkLimit ls) 10
  print $ sdrFinite (mkPlus (q 20) (q 0.5)) 2
  print $ sdrFinite (q 16) 2
  print $ sdrFinite (foldr1 mkPlus (replicate 10 (q (-2)))) 5
  print $ sdrFinite (foldr1 mkTimes (replicate 4 (q (-20)))) 5
  print $ sdrFinite (mkTimes (q 0.00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002) (q 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) 2

main' = print $ sdrFinite (foldr1 mkTimes (replicate 5 (mkRat (2)))) 5
