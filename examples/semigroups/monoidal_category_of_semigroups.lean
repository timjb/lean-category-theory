-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import ...category
import ...braided_monoidal_category
import .semigroups

namespace tqft.categories.examples.semigroups

universe variables u

open tqft.categories.monoidal_category

@[reducible] definition semigroup_product { α β : Type u } ( s : semigroup α ) ( t: semigroup β ) : semigroup (α × β) := {
  mul := λ p q, (p^.fst * q^.fst, p^.snd * q^.snd),
  -- From https://groups.google.com/d/msg/lean-user/bVs5FdjClp4/cbDZOqq_BAAJ
  mul_assoc := begin
                intros,
                simp [@mul.equations._eqn_1 (α × β)],
                dsimp,
                simp
              end
}

definition semigroup_morphism_product
  { α β γ δ : Type u }
  { s_f : semigroup α } { s_g: semigroup β } { t_f : semigroup γ } { t_g: semigroup δ }
  ( f : semigroup_morphism s_f t_f ) ( g : semigroup_morphism s_g t_g )
  : semigroup_morphism (semigroup_product s_f s_g) (semigroup_product t_f t_g) := {
  map := λ p, (f p.1, g p.2),
  multiplicative :=
    begin
      -- cf https://groups.google.com/d/msg/lean-user/bVs5FdjClp4/tfHiVjLIBAAJ
      intros,
      unfold mul has_mul.mul,
      dsimp,
      simp
    end
}


open tqft.categories.products

definition MonoidalCategoryOfSemigroups : MonoidalCategory := {
  CategoryOfSemigroups.{u} with
  tensor               := {
    onObjects     := λ p, ⟨ p.1.1 × p.2.1, semigroup_product p.1.2 p.2.2 ⟩,
    onMorphisms   := λ s t f, semigroup_morphism_product f.1 f.2,
    identities    := ♮,
    functoriality := ♮
  },
  tensor_unit          := ⟨ punit, trivial_semigroup ⟩, -- punit is just a universe-parameterized version of unit
  associator           := λ _ _ _, {
                                map := λ t, (t.1.1, (t.1.2, t.2)),
                                multiplicative := ♮
                              },
  backwards_associator := λ _ _ _, {
                                map := λ t, ((t.1, t.2.1), t.2.2),
                                multiplicative := ♮
                              },
  associators_inverses_1 := ♮,
  associators_inverses_2 := ♮
}

open tqft.categories.natural_transformation
open tqft.categories.braided_monoidal_category

definition BraidedMonoidalCategoryOfSemigroups : BraidedMonoidalCategory := {
  MonoidalCategoryOfSemigroups.{u} with
  braiding             := {
    morphism  := {
      components := λ _, {
                           map := λ p, (p.2, p.1),
                           multiplicative := ♮
                         },
      naturality := ♮
    },
    inverse   := {
      components := λ _, {
                           map := λ p, (p.2, p.1),
                           multiplicative := ♮
                         },
      naturality := ♮
    },
    witness_1 := ♮,
    witness_2 := ♮
  }
}

end tqft.categories.examples.semigroups