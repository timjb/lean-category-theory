-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison
import ..products

--set_option pp.universes true

open tqft.categories
open tqft.categories.functor
open tqft.categories.products
open tqft.categories.natural_transformation

namespace tqft.categories.monoidal_category

universe variables u v

@[reducible] definition TensorProduct ( C: Category ) := Functor ( C × C ) C

structure PreMonoidalCategory :=
  (category : Category)
  (tensor : TensorProduct category)
  (tensor_unit : category^.Obj)

namespace PreMonoidalCategory
  notation X `⊗` Y := (PreMonoidalCategory.tensor _)^.onObjects (X, Y)
  notation f `⊗` g := (PreMonoidalCategory.tensor _)^.onMorphisms (f, g)
end PreMonoidalCategory

instance PreMonoidalCategory_coercion : has_coe PreMonoidalCategory Category := 
  ⟨PreMonoidalCategory.category⟩

-- Copying fields. TODO: automate
@[reducible] definition PreMonoidalCategory.Obj      ( C : PreMonoidalCategory ) := @Category.Obj      C^.category
@[reducible] definition PreMonoidalCategory.Hom      ( C : PreMonoidalCategory ) := @Category.Hom      C^.category
@[reducible] definition PreMonoidalCategory.identity ( C : PreMonoidalCategory ) := @Category.identity C^.category
@[reducible] definition PreMonoidalCategory.compose  ( C : PreMonoidalCategory ) := @Category.compose  C^.category
@[reducible] definition PreMonoidalCategory.left_identity  ( C : PreMonoidalCategory ) := @Category.left_identity  C^.category
@[reducible] definition PreMonoidalCategory.right_identity ( C : PreMonoidalCategory ) := @Category.right_identity C^.category
@[reducible] definition PreMonoidalCategory.associativity  ( C : PreMonoidalCategory ) := @Category.associativity  C^.category

definition left_associated_triple_tensor ( C : PreMonoidalCategory.{ u v } ) : Functor ((C × C) × C) C :=
  FunctorComposition (C^.tensor × IdentityFunctor C) C^.tensor
definition right_associated_triple_tensor ( C : PreMonoidalCategory.{ u v } ) : Functor (C × (C × C)) C :=
  FunctorComposition (IdentityFunctor C × C^.tensor) C^.tensor

@[reducible] definition Associator ( C : PreMonoidalCategory.{ u v } ) := 
  NaturalTransformation 
    (left_associated_triple_tensor C) 
    (FunctorComposition (ProductCategoryAssociator C C C) (right_associated_triple_tensor C))

definition pentagon_3step_1 { C : PreMonoidalCategory.{ u v } } ( α : Associator.{ u v } C ) :=
  whisker_on_right
    (α × IdentityNaturalTransformation (IdentityFunctor C))
    C^.tensor

definition pentagon_3step_2 { C : PreMonoidalCategory.{ u v } } ( α : Associator.{ u v } C ) :=
  whisker_on_left
    (FunctorComposition
      (ProductCategoryAssociator C C C × IdentityFunctor C)
      ((IdentityFunctor C × C^.tensor) × IdentityFunctor C))
    α

definition pentagon_3step_3 { C : PreMonoidalCategory.{ u v } } ( α : Associator.{ u v } C ) :=
  whisker_on_left
    (FunctorComposition
      (ProductCategoryAssociator C C C × IdentityFunctor C)
      (ProductCategoryAssociator C (C × C) C))
    (whisker_on_right
      (IdentityNaturalTransformation (IdentityFunctor C) × α)
      C^.tensor)

definition pentagon_3step { C : PreMonoidalCategory.{ u v } } ( α : Associator.{ u v } C ) :=
  vertical_composition_of_NaturalTransformations
    (vertical_composition_of_NaturalTransformations
      (pentagon_3step_1 α)
      (pentagon_3step_2 α))
    (pentagon_3step_3 α)

definition pentagon_2step_1 { C : PreMonoidalCategory.{ u v } } ( α : Associator.{ u v } C ) :=
  whisker_on_left
    ((C^.tensor × IdentityFunctor C) × IdentityFunctor C)
    α

definition pentagon_2step_2 { C : PreMonoidalCategory.{ u v } } ( α : Associator.{ u v } C ) :=
  whisker_on_left
    (FunctorComposition
      (ProductCategoryAssociator (C × C) C C)
      (IdentityFunctor (C × C) × C^.tensor))
    α

definition pentagon_2step { C : PreMonoidalCategory.{ u v } } ( α : Associator.{ u v } C ) :=
  vertical_composition_of_NaturalTransformations
    (pentagon_2step_1 α)
    (pentagon_2step_2 α)

end tqft.categories.monoidal_category
