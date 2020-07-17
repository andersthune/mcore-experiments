lang Monoid
  -- A general monoid
  syn MVal =
  | MEmpty ()
  | MVal a
  | MAppend (MVal, MVal)

  sem mEval =
  | MVal a -> MVal a
  | a -> mAppend a -- To allow overriding mappend - i.e. Dual
  sem mAppend =
  | MAppend (a, b) -> mAppend (MAppend (mEval a, mEval b))

  sem mAlg =
  | a & !(MVal b) -> mAlg (mEval a)
  | MVal a -> a
end

lang Dual = Monoid
  -- The dual of a monoid, obtained by swapping the arguments to mappend
  sem mEval =
  | MAppend (a, b) -> mAppend (MAppend (mEval b, mEval a))
end

lang Sum = Monoid
  -- Integers as a monoid under addition
  sem mEval =
  | MEmpty () -> MVal 0
  sem mAppend =
  | MAppend (MVal i, MVal j) -> MVal (addi i j)
end

lang Prod = Monoid
  -- Integers as a monoid under multiplication
  sem mEval =
  | MEmpty () -> MVal 1
  sem mAppend =
  | MAppend (MVal i, MVal j) -> MVal (muli i j)
end

lang Endo = Monoid
  -- Functions over a given type as a monoid under composition
  sem mEval =
  | MEmpty () -> MVal identity
  sem mAppend =
  | MAppend (MVal f, MVal g) -> MVal (compose f g)
end

lang Free = Monoid
  -- Sequences as a monoid under concatenation
  sem mEval =
  | MEmpty () -> MVal []
  sem mAppend =
  | MAppend (MVal a, MVal b) -> MVal (concat a b)
end


lang FreeDual = Free + Dual

mexpr

use Free in
let x1 = mAlg (MAppend (MVal "Hello", MVal "World")) in
use FreeDual in
let x2 = mAlg (MAppend (MVal "Hello", MVal "World")) in
use Sum in
let y1 = mAlg (MAppend (MAppend (MVal 5, MVal 10), MEmpty ())) in
use Prod in
let y2 = mAlg (MAppend (MAppend (MVal 5, MVal 10), MEmpty ())) in

utest x1 with "HelloWorld" in
utest x2 with "WorldHello" in
utest y1 with 15 in
utest y2 with 50 in
()
