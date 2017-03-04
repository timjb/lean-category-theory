-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import ..monoidal_categories.monoidal_category
import .semigroups.semigroups

namespace tqft.categories.examples.types

open tqft.categories

@[reducible] definition { u } CategoryOfTypes : Category := 
{
    Obj := Type u,
    Hom := λ a b, a → b,

    identity := λ a, id,
    compose  := λ _ _ _ f g, g ∘ f,

    left_identity  := ♮,
    right_identity := ♮,
    associativity  := ♮
}

open tqft.categories.monoidal_category

definition TensorProductOfTypes : TensorProduct CategoryOfTypes :=
{
  onObjects     := λ p, prod p.1 p.2,
  onMorphisms   := λ _ _ p, λ q, (p.1 q.1, p.2 q.2),
  identities    := ♮,
  functoriality := ♮
}

definition TypeAssociator : Associator TensorProductOfTypes := {
  components := λ p, λ t, (t.1.1,(t.1.2, t.2)),
  naturality := ♮
}

definition LaxMonoidalCategoryOfTypes : LaxMonoidalCategory :=
{
    parent := CategoryOfTypes,
    tensor := TensorProductOfTypes,
    associator_transformation := TypeAssociator,
    pentagon := ♮
}

definition MonoidalCategoryOfTypes : MonoidalCategory :=
{
  parent := LaxMonoidalCategoryOfTypes,
  associator_is_isomorphism := {
    inverse := {
      components := λ p, λ t, ((t.1,t.2.1), t.2.2),
      naturality := ♮
    },
    witness_1 := ♮,
    witness_2 := ♮
  }
}

end tqft.categories.examples.types
