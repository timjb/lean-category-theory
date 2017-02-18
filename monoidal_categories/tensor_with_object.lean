-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison
import .monoidal_category

open tqft.categories
open tqft.categories.functor
open tqft.categories.products
open tqft.categories.natural_transformation

namespace tqft.categories.monoidal_category

universe variables u v

-- per https://groups.google.com/d/msg/lean-user/kkIFgWRJTLo/tr2VyJGmCQAJ
local attribute [reducible] lift_t coe_t coe_b

set_option pp.coercions false
set_option pp.notation true

definition tensor_on_left { C: MonoidalCategory.{u v} } ( Z: C^.Obj ) : Functor.{u v u v} C C :=
{
  onObjects := λ X, C^.tensorObjects Z X,
  onMorphisms := λ X Y f, C^.tensorMorphisms (C^.identity Z) f,
  identities := begin
                  blast,
                  rewrite - Functor.identities (C^.tensor),
                end,
  functoriality := begin
                      intros,
                      assert h : @Category.compose C = @MonoidalCategory.compose C, blast,
                      unfold MonoidalCategory.tensorMorphisms,
                      rewrite h,
                      rewrite - C^.interchange,
                      assert i : @Category.identity C = @MonoidalCategory.identity C, blast,
                      rewrite - i,
                      rewrite - h,
                      rewrite C^.parent^.parent^.category^.left_identity
                    end
}

definition tensor_on_right { C: MonoidalCategory.{u v} } ( Z: C^.Obj ) : Functor.{u v u v} C C :=
{
  onObjects := λ X, C^.tensorObjects X Z,
  onMorphisms := λ X Y f, C^.tensorMorphisms f (C^.identity Z),
  identities := begin
                  blast,
                  rewrite - Functor.identities (C^.tensor),  
                end,
  functoriality := begin
                      intros,
                      assert h : @Category.compose C = @MonoidalCategory.compose C, blast,
                      unfold MonoidalCategory.tensorMorphisms,
                      rewrite h,
                      rewrite - C^.interchange,
                      assert i : @Category.identity C = @MonoidalCategory.identity C, blast,
                      rewrite - i,
                      rewrite - h,
                      rewrite C^.parent^.parent^.category^.left_identity
                    end
}
  
end tqft.categories.monoidal_category
