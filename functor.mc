lang Functor
  syn Expr =
  sem fmap (f : a -> b) =
  | a -> a
end

lang Algebra = Functor
  syn Expr =
  | Val a
  -- alg : F a a -> a
  sem alg =
  | Val a -> a
  -- cata : Fix (F a) -> a
  sem cata =
  | a -> alg (fmap cata a)
end
