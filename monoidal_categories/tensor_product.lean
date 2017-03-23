-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison
import ..products

open tqft.categories
open tqft.categories.functor
open tqft.categories.products
open tqft.categories.natural_transformation

namespace tqft.categories.monoidal_category

universe variables u v

@[reducible] definition TensorProduct ( C: Category ) := Functor ( C × C ) C

@[reducible] definition left_associated_triple_tensor { C : Category.{ u v } } ( tensor : TensorProduct C ) : Functor ((C × C) × C) C :=
  FunctorComposition (tensor × IdentityFunctor C) tensor
@[reducible] definition right_associated_triple_tensor { C : Category.{ u v } } ( tensor : TensorProduct C ) : Functor (C × (C × C)) C :=
  FunctorComposition (IdentityFunctor C × tensor) tensor

@[reducible] definition Associator { C : Category.{u v} } ( tensor : TensorProduct C ) :=
  NaturalTransformation
    (left_associated_triple_tensor tensor)
    (FunctorComposition (ProductCategoryAssociator C C C) (right_associated_triple_tensor tensor))

end tqft.categories.monoidal_category
