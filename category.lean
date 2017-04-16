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

structure {u v} Category :=
  (Obj : Type u)
  (Hom : Obj → Obj → Type v)
  (identity : Π X : Obj, Hom X X)
  (compose  : Π { X Y Z : Obj }, Hom X Y → Hom Y Z → Hom X Z)

  (left_identity  : ∀ { X Y : Obj } (f : Hom X Y), compose (identity X) f = f)
  (right_identity : ∀ { X Y : Obj } (f : Hom X Y), compose f (identity Y) = f)
  (associativity  : ∀ { W X Y Z : Obj } (f : Hom W X) (g : Hom X Y) (h : Hom Y Z),
    compose (compose f g) h = compose f (compose g h))

attribute [simp] Category.left_identity
attribute [simp] Category.right_identity
attribute [ematch] Category.associativity
attribute [pointwise] Category.identity

-- instance Category_to_Hom : has_coe_to_fun Category :=
-- { F   := λ C, C.Obj → C.Obj → Type v,
--   coe := Category.Hom }

@[ematch] lemma Category.identity_idempotent
  ( C : Category )
  ( X : C.Obj ) : C.identity X = C.compose (C.identity X) (C.identity X) := ♮

open Category

lemma {u v} Category.congr_compose_right
  ( C : Category.{u v} )
  { X Y Z : C.Obj }
  { g h : C.Hom Y Z }
  ( f : C.Hom X Y )
  ( eq : g = h ) :
  C.compose f g = C.compose f h :=
  congr_arg (λ k, C.compose f k) eq

lemma {u v} Category.congr_compose_left
  ( C : Category.{u v} )
  { X Y Z : C.Obj }
  { f g : C.Hom X Y }
  ( h : C.Hom Y Z )
  ( eq : f = g ) :
  C.compose f h = C.compose g h :=
  congr_arg (λ k, C.compose k h) eq

lemma {u v} Category.congr_compose
  ( C : Category.{u v} )
  { X Y Z : C.Obj }
  { f1 f2 : C.Hom X Y }
  { g1 g2 : C.Hom Y Z }
  ( eqf : f1 = f2 )
  ( eqg : g1 = g2 ) :
  C.compose f1 g1 = C.compose f2 g2 :=
  eq.trans (C.congr_compose_left g1 eqf) (C.congr_compose_right f2 eqg)

-- TODO, eventually unify this code with the corresponding code for Graph, perhaps just by making Categories Graphs.
inductive {u v} morphism_path { C : Category.{u v} } : Obj C → Obj C → Type (max u v)
| nil  : Π ( h : C.Obj ), morphism_path h h
| cons : Π { h s t : C.Obj } ( e : C.Hom h s ) ( l : morphism_path s t ), morphism_path h t

notation a :: b := morphism_path.cons a b
notation `c[` l:(foldr `, ` (h t, morphism_path.cons h t) morphism_path.nil _ `]`) := l

definition {u v} concatenate_paths
 { C : Category.{u v} } :
 Π { x y z : C.Obj }, morphism_path x y → morphism_path y z → morphism_path x z
| ._ ._ _ (morphism_path.nil _)               q := q
| ._ ._ _ (@morphism_path.cons ._ _ _ _ e p') q := morphism_path.cons e (concatenate_paths p' q)

definition {u v} Category.compose_path ( C : Category.{u v} ) : Π { X Y : C.Obj }, morphism_path X Y → C.Hom X Y
| X ._  (morphism_path.nil ._)                := C.identity X
| _ _   (@morphism_path.cons ._ ._ _ ._ e p)  := C.compose e (Category.compose_path p)

end tqft.categories
