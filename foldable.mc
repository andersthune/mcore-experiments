include "monoid.mc"

lang EndoDual = Endo + Dual

lang Foldable = Monoid
  -- Foldables
  syn Fold =
  | Fold a
  | FoldMap ((b -> m), a)
  syn FoldF =
  | Foldr ((b -> c -> c), c, a)
  | Foldl ((c -> b -> c), c, a)

  sem fAlg =
  | a -> defaultFAlg a
  sem defaultFAlg =
  | Fold l -> fAlg (FoldMap (identity, l))
  | FoldMap (f, l) -> foldF (Foldr (lam x. lam y. MAppend(f x, y), MEmpty (), l))

  sem foldF =
  | a -> defaultFoldF a
  sem defaultFoldF =
  | Foldr (f, z, l) -> use Endo in
    mAlg (fAlg (FoldMap (lam x. MVal (f x), l))) z
  | Foldl (f, z, l) -> use EndoDual in
    let flip = lam f. lam x. lam y. f y x in
    mAlg (fAlg (FoldMap (lam x. MVal (flip f x), l))) z
end

lang FoldableSeq = Foldable
  -- Sequences as foldables
  sem foldF =
  | Foldr (f, z, l) -> foldr f z l
end

lang SumSeq = Sum + FoldableSeq
lang ProdSeq = Prod + FoldableSeq

mexpr

use SumSeq in
let x1 = mAlg (fAlg (FoldMap (lam x. MVal x, [1,2,3,4]))) in
use ProdSeq in
let x2 = mAlg (fAlg (FoldMap (lam x. MVal x, [1,2,3,4]))) in

use FoldableSeq in
let y1 = foldF (Foldr (concat, "", ["Hello", " ", "World"])) in
let y2 = foldF (Foldl (concat, "", ["Hello", " ", "World"])) in

utest x1 with 10 in
utest x2 with 24 in
utest y1 with "Hello World" in
utest y2 with "Hello World" in
()
