include "monoid.mc"

lang Foldable = Monoid
  -- Foldables
  syn Fold =
  | Fold a
  | FoldMap ((b -> m), a)
  sem fAlg =
  | Fold l -> fAlg (FoldMap (identity, l))
end

lang FoldrEndo = Foldable + Endo
  -- A language providing Foldr for general foldables
  syn FoldFun =
  | FoldF ((b -> c -> c), c, a)
  sem foldF =
  | FoldF (f, z, l) -> mAlg (fAlg (FoldMap (lam x. MVal (f x), l))) z
end

lang FoldlEndo = Foldable + Endo + Dual
  -- A language providing Foldl for general foldables
  syn FoldFun =
  | FoldF ((c -> b -> c), c, a)
  sem foldF =
  | FoldF (f, z, l) -> let flip = lam f. lam x. lam y. f y x in
    mAlg (fAlg (FoldMap (lam x. MVal (flip f x), l))) z
end

lang FoldableSeq = Foldable
  -- Sequences as foldables
  sem fAlg =
  | FoldMap (f, l) -> let mappend = lam a. lam b. MAppend (a, b) in
     mEval (foldr mappend (MEmpty ()) (map f l))
end

lang SumSeq = Sum + FoldableSeq
lang ProdSeq = Prod + FoldableSeq

lang FoldrSeq = FoldrEndo + FoldableSeq
lang FoldlSeq = FoldlEndo + FoldableSeq

mexpr

use SumSeq in
let x1 = mAlg (fAlg (FoldMap (lam x. MVal x, [1,2,3,4]))) in
use ProdSeq in
let x2 = mAlg (fAlg (FoldMap (lam x. MVal x, [1,2,3,4]))) in

use FoldrSeq in
let y1 = foldF (FoldF (concat, "", ["Hello", " ", "World"])) in
use FoldlSeq in
let y2 = foldF (FoldF (concat, "", ["Hello", " ", "World"])) in

utest x1 with 10 in
utest x2 with 24 in
utest y1 with "Hello World" in
utest y2 with "Hello World" in
()
