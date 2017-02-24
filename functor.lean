-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import .category

open tqft.categories

namespace tqft.categories.functor

variable { Obj₁ : Type* }
variable { Obj₂ : Type* }
variable { Obj₃ : Type* }
variable ( C : Obj₁ → Obj₁ → Type* )
variable ( D : Obj₂ → Obj₂ → Type* )
variable ( E : Obj₃ → Obj₃ → Type* )

structure Functor [ sC : category C ] [ sD : category D ]:=
  (onObjects : Obj₁ → Obj₂)
  (onMorphisms : Π { X Y : Obj₁ }, C X Y → D (onObjects X) (onObjects Y))
  (identities : ∀ ( X : Obj₁ ),
    onMorphisms (sC^.identity X) = sD^.identity (onObjects X))
  (functoriality : ∀ { X Y Z : Obj₁ } (f : C X Y) (g : C Y Z),
    onMorphisms (sC^.compose f g) = sD^.compose (onMorphisms f) (onMorphisms g))

attribute [class] Functor
attribute [simp] Functor.identities
attribute [simp] Functor.functoriality

-- We define a coercion so that we can write `F X` for the functor `F` applied to the object `X`.
-- One can still write out `onObjects F X` when needed.
--instance Functor_to_onObjects [ F : Functor Hom₁ Hom₂ ] : has_coe_to_fun F :=
--{ F   := λ f, C^.Obj → D^.Obj,
--  coe := Functor.onObjects }

/-
-- Unfortunately we haven't been able to set up similar notation for morphisms.
-- Instead we define notation so that `F <$> f` denotes the functor `F` applied to the morphism `f`.
-- One can still write out `onMorphisms F f` when needed, or even the very verbose `@Functor.onMorphisms C D F X Y f`.
--namespace notations
  -- Lean complains about the use of local variables in
  -- notation. There must be a way around that.
  infix `<$>` :50 := λ {C : Category} {D : Category}
                       (F : Functor C D) {X Y : C^.Obj} (f : C^.Hom X Y),
                       Functor.onMorphisms F f
end notations

open notations
-/

-- This defines a coercion allowing us to write `F f` for `onMorphisms F f`
-- but sadly it doesn't work if to_onObjects is already in scope.
-- instance Functor_to_onMorphisms { C D : Category } : has_coe_to_fun (Functor C D) :=
-- { F   := λ f, Π ⦃X Y : C^.Obj⦄, C^.Hom X Y → D^.Hom (f X) (f Y), -- contrary to usual use, `f` here denotes the Functor.
--  coe := Functor.onMorphisms }

@[reducible] instance identityFunctor [ sC : category C ] :
  Functor C C :=
{
  onObjects     := id,
  onMorphisms   := λ _ _ f, f,
  identities    := ♮,
  functoriality := ♮
}


variable F [ sC : category C ] [ sD : category D ] : Functor C D
variable G [ sD : category D ] [ sE : category E ] : Functor D E

@[reducible] instance FunctorComposition
  [ sC : category C ] [ sD : category D ] [ sE : category E ]
  ( F : Functor Hom₁ Hom₂ ) ( G : Functor Hom₂ Hom₃ ) : Functor Hom₁ Hom₃ :=
{
  onObjects     := λ X, G^.onObjects (F^.onObjects X),
  onMorphisms   := λ _ _ f, G^.onMorphisms (F^.onMorphisms f),
  identities    := ♮,
  functoriality := ♮
}

--namespace Functor
--  notation F `∘` G := FunctorComposition F G
--end Functor

-- We'll want to be able to prove that two functors are equal if they are equal on objects and on morphisms.
-- Implementation warning:
-- When using `apply Functors_pointwise_equal`, you might expect that Lean will create two goals,
--   one for `objectWitness`, and one for `morphismWitness`.
--   However, because `morphismWitness` depends on `objectWitness`, it will actually only create the goal
--   for `morphismWitness`, leaving the `objectWitness` goal somehow "implicit" and likely unprovable.
--   See https://groups.google.com/d/msg/lean-user/bhStu87PjiI/vqsyr9ZABAAJ for details.
-- If you run into this problem, use `fapply Functors_pointwise_equal` instead.
@[pointwise_2] lemma Functors_pointwise_equal
  { C D : Category } 
  { F G : Functor C D } 
  ( objectWitness : ∀ X : C^.Obj, F^.onObjects X = G^.onObjects X ) 
  ( morphismWitness : ∀ X Y : C^.Obj, ∀ f : C^.Hom X Y, ⟦ F^.onMorphisms f ⟧  = G^.onMorphisms f ) : F = G :=
begin
  induction F with F_onObjects F_onMorphisms,
  induction G with G_onObjects G_onMorphisms,
  assert h_objects : F_onObjects = G_onObjects, exact funext objectWitness,
  subst h_objects,
  assert h_morphisms : @F_onMorphisms = @G_onMorphisms, 
  apply funext, intro X, apply funext, intro Y, apply funext, intro f,
  exact morphismWitness X Y f,
  subst h_morphisms
end

lemma FunctorComposition_left_identity [ C : category Hom₁ ] [ D : category Hom₂ ]
  ( F : Functor Hom₁ Hom₂ ) :
  FunctorComposition (IdentityFunctor Hom₁) F = F := ♮

lemma FunctorComposition_right_identity [ C : category Hom₁ ] [ D : category Hom₂ ]
  ( F : Functor Hom₁ Hom₂ ) :
  FunctorComposition F (IdentityFunctor D) = F := ♮

lemma FunctorComposition_associative { B C D E : Category } ( F : Functor B C ) ( G : Functor C D ) ( H : Functor D E ) :
  FunctorComposition (FunctorComposition F G) H = FunctorComposition F (FunctorComposition G H) := ♮

end tqft.categories.functor
