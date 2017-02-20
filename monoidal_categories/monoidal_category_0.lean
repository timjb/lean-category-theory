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

-- Convenience methods which take two arguments, rather than a pair. (This seems to often help the elaborator avoid getting stuck on `prod.mk`.)
@[reducible] definition PreMonoidalCategory.tensorObjects   ( C : PreMonoidalCategory ) ( X Y : C^.Obj ) : C^.Obj := C^.tensor (X, Y)
@[reducible] definition PreMonoidalCategory.tensorMorphisms ( C : PreMonoidalCategory ) { W X Y Z : C^.Obj } ( f : C^.Hom W X ) ( g : C^.Hom Y Z ) : C^.Hom (C^.tensor (W, Y)) (C^.tensor (X, Z)) := C^.tensor^.onMorphisms (f, g)

definition left_associated_triple_tensor ( C : PreMonoidalCategory.{ u v } ) : Functor ((C × C) × C) C :=
  FunctorComposition (C^.tensor × IdentityFunctor C) C^.tensor
definition right_associated_triple_tensor ( C : PreMonoidalCategory.{ u v } ) : Functor (C × (C × C)) C :=
  FunctorComposition (IdentityFunctor C × C^.tensor) C^.tensor

@[reducible] definition Associator ( C : PreMonoidalCategory.{ u v } ) := 
  NaturalTransformation 
    (left_associated_triple_tensor C) 
    (FunctorComposition (ProductCategoryAssociator C C C) (right_associated_triple_tensor C))

definition Pentagon { C: PreMonoidalCategory } ( associator : Associator C ) :=
  let α ( X Y Z : C^.Obj ) := associator ((X, Y), Z) in
  ∀ W X Y Z : C^.Obj, 
    C^.compose (α (W ⊗ X) Y Z) (α W X (Y ⊗ Z))
  = C^.compose (C^.compose (C^.tensorMorphisms (α W X Y) (C^.identity Z)) (α W (X ⊗ Y) Z)) (C^.tensorMorphisms (C^.identity W) (α X Y Z)) 

end tqft.categories.monoidal_category
