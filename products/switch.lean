-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison
import .products

open tqft.categories
open tqft.categories.functor
open tqft.categories.natural_transformation

namespace tqft.categories.products

definition SwitchProductCategory ( C D : Category ) : Functor (C × D) (D × C) :=
{
  onObjects     := λ X, (X.snd, X.fst),
  onMorphisms   := λ _ _ f, (f.snd, f.fst),
  identities    := ♮,
  functoriality := ♮
}

definition SwitchSymmetry ( C D : Category ) : NaturalIsomorphism (FunctorComposition (SwitchProductCategory C D) (SwitchProductCategory D C)) (IdentityFunctor (C × D)) := ♯

end tqft.categories.products
