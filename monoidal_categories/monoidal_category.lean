-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison
import .tensor_product

open tqft.categories
open tqft.categories.functor
open tqft.categories.products
open tqft.categories.natural_transformation

namespace tqft.categories.monoidal_category

universe variables u v

structure LaxMonoidalCategory
  extends carrier : Category :=
  (tensor                    : TensorProduct carrier)
  (associator_transformation : Associator tensor)

-- TODO Unfortunately we need to copy these attributes; this isn't handled by inheritance.
attribute [ematch,simp] LaxMonoidalCategory.left_identity
attribute [ematch,simp] LaxMonoidalCategory.right_identity
attribute [ematch] LaxMonoidalCategory.associativity

instance LaxMonoidalCategory_coercion : has_coe LaxMonoidalCategory.{u v} Category.{u v} :=
  ⟨LaxMonoidalCategory.to_Category⟩

structure MonoidalCategory
  extends LaxMonoidalCategory :=
  (associator_is_isomorphism   : is_NaturalIsomorphism associator_transformation)

-- TODO Unfortunately we need to copy these attributes; this isn't handled by inheritance.
attribute [ematch,simp] MonoidalCategory.left_identity
attribute [ematch,simp] MonoidalCategory.right_identity
attribute [ematch] MonoidalCategory.associativity

instance MonoidalCategory_coercion_to_LaxMonoidalCategory   : has_coe MonoidalCategory.{u v} LaxMonoidalCategory.{u v}   := ⟨MonoidalCategory.to_LaxMonoidalCategory⟩

end tqft.categories.monoidal_category
