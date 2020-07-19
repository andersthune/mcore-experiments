include "monoid.mc"

let seq_foldr = foldr
let flip = lam f. lam x. lam y. f y x

lang EndoDual = Endo + Dual

-- Foldable t = Monoid m
lang Foldable = Monoid
  -- Foldables
  syn Fold = -- Fold a

  sem fold =
  | fld -> foldMap identity fld

  sem foldMap (f : a -> F) =
  | fld -> foldr (lam x. lam y. MAppend (f x, y)) (MEmpty ()) fld

  sem foldr (f : a -> b -> b) (z : b) =
  | fld -> use Endo in
    cata (foldMap (lam x. Val (f x)) fld) z

  sem foldl (f : b -> a -> b) (z : b) =
  | fld -> use EndoDual in
    cata (foldMap (lam x. Val (flip f x)) fld) z

  sem autoFold =
  | fld -> foldMap (lam x. Val x) fld
end

lang FoldableSeq = Foldable
  syn Fold =
  | Seq [a]
  -- Sequences as foldables
  sem foldr (f : a -> b -> b) (z : b) =
  | Seq l -> seq_foldr f z l
end

lang SumSeq = Sum + FoldableSeq
lang ProdSeq = Prod + FoldableSeq

mexpr

use SumSeq in
let x1 = cata (foldMap (lam x. Val x) (Seq [1,2,3,4])) in
use ProdSeq in
let x2 = cata (foldMap (lam x. Val x) (Seq [1,2,3,4])) in
let x3 = cata (autoFold (Seq [1,2,3,4])) in

use FoldableSeq in
let y1 = foldr concat "" (Seq ["Hello", " ", "World"]) in
let y2 = foldr concat "" (Seq ["Hello", " ", "World"]) in

utest x1 with 10 in
utest x2 with 24 in
utest x3 with 24 in
utest y1 with "Hello World" in
utest y2 with "Hello World" in
()
