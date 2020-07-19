lang Functor
  syn F =
  sem fmap (f : a -> b) =
end

lang Algebra = Functor
  syn F =
  | Val a
  sem fmap (f : a -> b) =
  | a -> a
  -- alg : F a a -> a
  sem alg =
  | Val a -> a
  -- cata : Fix (F a) -> a
  sem cata =
  | a -> alg (fmap cata a)
end
