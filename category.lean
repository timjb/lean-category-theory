-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import .tactics

/-
-- We've decided that Obj and Hom should be fields of Category, rather than parameters.
-- Mostly this is for the sake of simpler signatures, but it's possible that it is not the right choice.
-- Functor and NaturalTransformation are each parameterized by both their source and target.
-/

namespace tqft.categories

universe variables u v

structure category {Obj : Type*} (Hom : Obj → Obj → Type*) :=
  (identity : Π X : Obj, Hom X X)
  (compose  : Π { X Y Z : Obj }, Hom X Y → Hom Y Z → Hom X Z)

  (left_identity  : ∀ { X Y : Obj } ( f : Hom X Y ), compose (identity _) f = f)
  (right_identity : ∀ { X Y : Obj } ( f : Hom X Y ), compose f (identity _) = f)
  (associativity  : ∀ { W X Y Z : Obj } ( f : Hom W X ) ( g : Hom X Y ) ( h : Hom Y Z ),
    compose (compose f g) h = compose f (compose g h))

attribute [class] category
attribute [simp] category.left_identity
attribute [simp] category.right_identity

namespace category
  notation f `∘` g := category.compose _ f g
end category

structure Category :=
  (Obj : Type u)
  (Hom : Obj → Obj → Type v) 
  (identity : Π X : Obj, Hom X X)
  (compose  : Π { X Y Z : Obj }, Hom X Y → Hom Y Z → Hom X Z)

  (left_identity  : ∀ { X Y : Obj } (f : Hom X Y), compose (identity _) f = f)
  (right_identity : ∀ { X Y : Obj } (f : Hom X Y), compose f (identity _) = f)
  (associativity  : ∀ { W X Y Z : Obj } (f : Hom W X) (g : Hom X Y) (h : Hom Y Z),
    compose (compose f g) h = compose f (compose g h))


instance Category_to_Hom : has_coe_to_fun Category :=
{ F   := λ C, C^.Obj → C^.Obj → Type v,
  coe := Category.Hom }

-- attribute [class] Category
/-
-- Unfortunately declaring Category as a class when it is first declared results
-- in an unexpected type signature; this is a feature, not a bug, as Stephen discovered
-- and explained at https://github.com/semorrison/proof/commit/e727197e794647d1148a1b8b920e7e567fb9079f
--
-- We just declare things as structures, and then add the class attribute afterwards.
-/

variable { Obj : Type* }
variable Hom : Obj → Obj → Type*
variable [ C : category Hom ]
include C
variables { X Y Z : Obj }

structure Isomorphism (morphism : Hom X Y) :=
  (inverse : Hom Y X)
  (witness_1 : C^.compose morphism inverse = C^.identity X)
  (witness_2 : C^.compose inverse morphism = C^.identity Y)

attribute [class] Isomorphism
attribute [simp] Isomorphism.witness_1
attribute [simp] Isomorphism.witness_2

instance Isomorphism_coercion_to_morphism { X Y : Obj } ( f : Hom X Y ) :
  has_coe (Isomorphism Hom f) (Hom X Y) :=
{ coe := λ _, f }
  
end tqft.categories
