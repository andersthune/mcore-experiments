include "monoid.mc"

let seq_foldr = foldr
let flip = lam f. lam x. lam y. f y x

lang EndoDual = Endo + Dual

-- Foldable t = Monoid m
lang Foldable = Monoid
  -- Foldables
  syn Fold = -- Fold a
  | Fold t -- Fold (t a)

  sem fold =
  | fld -> foldMap identity fld

  sem foldMap (f : a -> MVal) =
  | fld -> foldr (lam x. lam y. MAppend (f x, y)) (MEmpty ()) fld

  sem foldr (f : a -> b -> b) (z : b) =
  | fld -> use Endo in
    mAlg (foldMap (lam x. MVal (f x)) fld) z

  sem foldl (f : b -> a -> b) (z : b) =
  | fld -> use EndoDual in
    mAlg (foldMap (lam x. MVal (flip f x)) fld) z

  sem autoFold =
  | fld -> foldMap (lam x. MVal x) fld
end

lang FoldableSeq = Foldable
  -- Sequences as foldables
  sem foldr (f : a -> b -> b) (z : b) =
  | Fold l -> seq_foldr f z l
end

lang SumSeq = Sum + FoldableSeq
lang ProdSeq = Prod + FoldableSeq

mexpr

use SumSeq in
let x1 = mAlg (foldMap (lam x. MVal x) (Fold [1,2,3,4])) in
use ProdSeq in
let x2 = mAlg (foldMap (lam x. MVal x) (Fold [1,2,3,4])) in
let x3 = mAlg (autoFold (Fold [1,2,3,4])) in

use FoldableSeq in
let y1 = foldr concat "" (Fold ["Hello", " ", "World"]) in
let y2 = foldr concat "" (Fold ["Hello", " ", "World"]) in

utest x1 with 10 in
utest x2 with 24 in
utest x3 with 24 in
utest y1 with "Hello World" in
utest y2 with "Hello World" in
()
