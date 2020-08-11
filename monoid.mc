include "functor.mc"

lang Monoid = Algebra
  -- A general monoid
  syn Expr =
  | MEmpty ()
  | MAppend (b, b)

  sem fmap (f : a -> b) =
  | MAppend (a, b) -> MAppend (f a, f b)
  sem alg =
  | a -> mappend a -- To allow overriding mappend; i.e Dual
  sem mappend =
end

lang Dual = Monoid
  -- The dual of a monoid, obtained by swapping the arguments to mappend
  sem alg =
  | MAppend (a, b) -> mappend (MAppend (b, a))
end

lang Sum = Monoid
  -- Integers as a monoid under addition
  sem alg =
  | MEmpty () -> 0
  sem mappend =
  | MAppend (i, j) -> addi i j
end

lang Prod = Monoid
  -- Integers as a monoid under multiplication
  sem alg =
  | MEmpty () -> 1
  sem mappend =
  | MAppend (i, j) -> muli i j
end

lang Endo = Monoid
  -- Functions over a given type as a monoid under composition
  sem alg =
  | MEmpty () -> identity
  sem mappend =
  | MAppend (f, g) -> compose f g
end

lang Free = Monoid
  -- Sequences as a monoid under concatenation
  sem alg =
  | MEmpty () -> []
  sem mappend =
  | MAppend (a, b) -> concat a b
end


lang FreeDual = Free + Dual

mexpr

use Free in
let x1 = cata (MAppend (Val "Hello", Val "World")) in
use FreeDual in
let x2 = cata (MAppend (Val "Hello", Val "World")) in
use Sum in
let y1 = cata (MAppend (MAppend (Val 5, Val 10), MEmpty ())) in
use Prod in
let y2 = cata (MAppend (MAppend (Val 5, Val 10), MEmpty ())) in

utest x1 with "HelloWorld" in
utest x2 with "WorldHello" in
utest y1 with 15 in
utest y2 with 50 in
()
