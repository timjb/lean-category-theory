-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison
import .monoidal_category

namespace tqft.categories.braided_monoidal_category

open tqft.categories
open tqft.categories.functor
open tqft.categories.natural_transformation
open tqft.categories.products
open tqft.categories.monoidal_category

universe variables u v

/-
-- I don't really understand why the universe annotations are needed in Braiding and in squaredBraiding.
-- My guess is that it is related to
-- https://groups.google.com/d/msg/lean-user/3qzchWkut0g/0QR6_cS8AgAJ
-/

definition Braiding(C : MonoidalCategory.{u v}) := 
  NaturalIsomorphism (C^.tensor) (FunctorComposition (SwitchProductCategory C C) C^.tensor)

structure BraidedMonoidalCategory :=
  (parent: MonoidalCategory)
  (braiding: Braiding parent)
-- TODO hexagon!

-- Copying fields. TODO: automate
@[reducible] definition BraidedMonoidalCategory.Obj                       ( C : BraidedMonoidalCategory ) := @MonoidalCategory.Obj                       C^.parent
@[reducible] definition BraidedMonoidalCategory.Hom                       ( C : BraidedMonoidalCategory ) := @MonoidalCategory.Hom                       C^.parent
@[reducible] definition BraidedMonoidalCategory.identity                  ( C : BraidedMonoidalCategory ) := @MonoidalCategory.identity                  C^.parent
@[reducible] definition BraidedMonoidalCategory.compose                   ( C : BraidedMonoidalCategory ) := @MonoidalCategory.compose                   C^.parent
@[reducible] definition BraidedMonoidalCategory.tensor                    ( C : BraidedMonoidalCategory ) := @MonoidalCategory.tensor                    C^.parent
@[reducible] definition BraidedMonoidalCategory.associator_transformation ( C : BraidedMonoidalCategory ) := @MonoidalCategory.associator_transformation C^.parent
@[reducible] definition BraidedMonoidalCategory.associator_is_isomorphism ( C : BraidedMonoidalCategory ) := @MonoidalCategory.associator_is_isomorphism C^.parent

instance BraidedMonoidalCategory_coercion_to_MonoidalCategory : has_coe BraidedMonoidalCategory MonoidalCategory := ⟨BraidedMonoidalCategory.parent⟩

-- TODO think about where these should properly live.
lemma FunctorComposition_left_identity { C D : Category } ( F : Functor C D ) :
  FunctorComposition (IdentityFunctor C) F = F := ♮

lemma FunctorComposition_right_identity { C D : Category } ( F : Functor C D ) :
  FunctorComposition F (IdentityFunctor D) = F := ♮

lemma FunctorComposition_associative { B C D E : Category } ( F : Functor B C ) ( G : Functor C D ) ( H : Functor D E ) :
  FunctorComposition (FunctorComposition F G) H = FunctorComposition F (FunctorComposition G H) := ♮

@[reducible] definition squared_Braiding { C : MonoidalCategory.{u v} } ( braiding : Braiding C )
  : NaturalTransformation C^.tensor C^.tensor :=
  begin
    pose square := vertical_composition_of_NaturalTransformations braiding^.morphism (whisker_on_left (SwitchProductCategory C C) braiding^.morphism),
    rewrite - FunctorComposition_associative at square,
    erewrite switch_twice_is_the_identity at square,
    rewrite FunctorComposition_left_identity at square,
    exact square
  end 

@[reducible] definition Symmetry(C : BraidedMonoidalCategory) : Prop :=
  squared_Braiding (C^.braiding) = IdentityNaturalTransformation C^.tensor

structure SymmetricMonoidalCategory :=
  (parent: BraidedMonoidalCategory)
  (symmetry: Symmetry parent)

end tqft.categories.braided_monoidal_category