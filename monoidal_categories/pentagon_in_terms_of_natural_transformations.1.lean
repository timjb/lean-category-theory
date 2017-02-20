-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison
import .monoidal_category
import .pentagon_in_terms_of_natural_transformations

--set_option pp.universes true

open tqft.categories
open tqft.categories.functor
open tqft.categories.products
open tqft.categories.natural_transformation

namespace tqft.categories.monoidal_category

lemma pentagon_in_terms_of_natural_transformations
  ( C : MonoidalCategory ) : pentagon_2step C^.associator_transformation = pentagon_3step C^.associator_transformation :=
  begin
    -- unfold pentagon_2step,
    -- unfold pentagon_3step,
    blast,
    -- apply C^.pentagon
    exact sorry
  end

end tqft.categories.monoidal_category