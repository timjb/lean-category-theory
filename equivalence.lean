-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import .natural_transformation
import .isomorphism

open tqft.categories
open tqft.categories.isomorphism
open tqft.categories.functor
open tqft.categories.natural_transformation

namespace tqft.categories.equivalence

structure {u1 v1 u2 v2} Equivalence ( C : Category.{u1 v1} ) ( D : Category.{u2 v2} ) :=
  ( functor : Functor C D )
  ( inverse : Functor D C )
  ( isomorphism_1 : NaturalIsomorphism (FunctorComposition functor inverse) (IdentityFunctor C) )
  ( isomorphism_2 : NaturalIsomorphism (FunctorComposition inverse functor) (IdentityFunctor D) )

definition {u1 v1 u2 v2} is_Equivalence { C : Category.{u1 v1} } { D : Category.{u2 v2} } ( F : Functor C D ) := { e : Equivalence C D // e.functor = F }

definition {u1 v1 u2 v2} Equivalence.reverse { C : Category.{u1 v1} } { D : Category.{u2 v2} } ( e : Equivalence C D ) : Equivalence D C :=
{
  functor := e.inverse,
  inverse := e.functor,
  isomorphism_1 := e.isomorphism_2,
  isomorphism_2 := e.isomorphism_1
}

structure {u1 v1 u2 v2} Full     { C : Category.{u1 v1} } { D : Category.{u2 v2} } ( F : Functor C D ) :=
  ( preimage : ∀ { X Y : C.Obj } ( f : D.Hom (F X) (F Y) ), C.Hom X Y )
  ( witness  : ∀ { X Y : C.Obj } ( f : D.Hom (F X) (F Y) ), F.onMorphisms (preimage f) = f )

attribute [pointwise] Full.preimage
attribute [simp,ematch] Full.witness

structure {u1 v1 u2 v2} Faithful { C : Category.{u1 v1} } { D : Category.{u2 v2} } ( F : Functor C D ) :=
  ( injectivity : ∀ { X Y : C.Obj } ( f g : C.Hom X Y ) ( p : F.onMorphisms f = F.onMorphisms g ), f = g )

attribute [pointwise] Faithful.injectivity

definition {u1 v1 u2 v2} Embedding { C : Category.{u1 v1} } { D : Category.{u2 v2} } ( F : Functor C D ) := (Full F) × (Faithful F)

definition {u1 v1 u2 v2} EssentiallySurjective { C : Category.{u1 v1} } { D : Category.{u2 v2} } ( F : Functor C D ) := Π d : D.Obj, Σ c : C.Obj, Isomorphism D (F c) d

lemma Equivalences_are_EssentiallySurjective { C D : Category } ( e : Equivalence C D ) : EssentiallySurjective (e.functor) :=
  λ Y : D.Obj, ⟨ e.inverse Y, e.isomorphism_2.components Y ⟩

-- These is an annoying hack, because I can't simplify hypotheses automatically. FIXME
lemma {u1 v1} IdentityFunctor_is_identity { C : Category.{u1 v1} } { X Y : C.Obj } ( f : C.Hom X Y ) : (IdentityFunctor C).onMorphisms f = f := ♯
lemma {u1 v1 u2 v2 u3 v3} FunctorComposition_is_composition 
  { C : Category.{u1 v1} }
  { D : Category.{u2 v2} }
  { E : Category.{u3 v3} }
  { F : Functor C D }
  { G : Functor D E }
  { X Y : C.Obj }
  { f : C.Hom X Y } :
  (FunctorComposition F G).onMorphisms f = G.onMorphisms (F.onMorphisms f) := ♯

section Equivalences_are_FullyFaithful
  universes u1 v1 u2 v2
  parameters { C : Category.{u1 v1} } { D : Category.{u2 v2} }
  parameter ( e : Equivalence C D )

  definition F : Functor C D := e.functor
  definition G : Functor D C := e.inverse
  definition η : NaturalIsomorphism (FunctorComposition F G) (IdentityFunctor C) := e.isomorphism_1
  definition ε : NaturalIsomorphism (FunctorComposition G F) (IdentityFunctor D) := e.isomorphism_2

  local infixl `⟩C⟩`:60 := C.compose
  local infixl `⟩D⟩`:60 := D.compose

  definition image { X Y : C.Obj } ( h : C.Hom X Y ) : D.Hom (F X) (F Y) :=
    F.onMorphisms h

  private definition preimage1 ( X Y : C.Obj ) ( h : D.Hom (F X) (F Y) ) : C.Hom X Y :=
    (η.inverse.components X ⟩C⟩ G.onMorphisms h) ⟩C⟩ η.morphism.components Y

  lemma preimage1_is_retraction ( X Y : C.Obj ) ( h : C.Hom X Y ) : preimage1 X Y (image h) = h :=
    η.naturality_1 h

  private definition preimage2 ( S T : D.Obj ) ( g : D.Hom (F (G S)) (F (G T)) ) : C.Hom (G S) (G T) :=
    let g' : D.Hom S T := ε.inverse.components S ⟩D⟩ g ⟩D⟩ ε.morphism.components T
    in G.onMorphisms g'

  lemma preimage2_is_section ( S T : D.Obj ) ( g : D.Hom (F (G S)) (F (G T)) ) : image (preimage2 S T g) = g :=
    let g' := ε.inverse.components S ⟩D⟩ g ⟩D⟩ ε.morphism.components T in
    calc
      (FunctorComposition G F).onMorphisms g'
          =
      ε.morphism.components S ⟩D⟩ g' ⟩D⟩ ε.inverse.components T
          : eq.symm (NaturalIsomorphism.naturality_1 (Isomorphism.reverse ε) g')
      ... =
      ε.morphism.components S ⟩D⟩ (ε.inverse.components S ⟩D⟩ g ⟩D⟩ ε.morphism.components T) ⟩D⟩ ε.inverse.components T
          : by reflexivity
      ... =
      (ε.morphism.components S ⟩D⟩ ε.inverse.components S) ⟩D⟩ g ⟩D⟩ (ε.morphism.components T ⟩D⟩ ε.inverse.components T)
          : ♮
      ... =
      D.identity _ ⟩D⟩ g ⟩D⟩ D.identity _
          : D.congr_compose
              (D.congr_compose_left g (ε.componentwise_witness_1 S))
              (ε.componentwise_witness_1 T)
      ... =
      g
          : ♮

  private definition preimage3 ( X Y : C.Obj ) ( h : D.Hom (F X) (F Y) ) : C.Hom X Y :=
    let h' := F.onMorphisms (η.morphism.components X) ⟩D⟩ h ⟩D⟩ F.onMorphisms (η.inverse.components Y)
    in η.inverse.components X ⟩C⟩ preimage2 (F X) (F Y) h' ⟩C⟩ η.morphism.components Y

  lemma preimage3_is_section ( X Y : C.Obj ) ( h : D.Hom (F X) (F Y) ) : image (preimage3 X Y h) = h :=
    let h' := F.onMorphisms (η.morphism.components X) ⟩D⟩ h ⟩D⟩ F.onMorphisms (η.inverse.components Y) in
    calc
      image (preimage3 X Y h)
          =
      F.onMorphisms (η.inverse.components X ⟩C⟩ preimage2 (F X) (F Y) h' ⟩C⟩ η.morphism.components Y)
          : by reflexivity
      ... =
      F.onMorphisms (η.inverse.components X) ⟩D⟩ F.onMorphisms (preimage2 (F X) (F Y) h') ⟩D⟩ F.onMorphisms (η.morphism.components Y)
          : ♮
      ... =
      F.onMorphisms (η.inverse.components X) ⟩D⟩ h' ⟩D⟩ F.onMorphisms (η.morphism.components Y)
          : D.congr_compose_left _ (D.congr_compose_right _ (preimage2_is_section _ _ h'))
      ... =
      F.onMorphisms (η.inverse.components X) ⟩D⟩ (F.onMorphisms (η.morphism.components X) ⟩D⟩ h ⟩D⟩ F.onMorphisms (η.inverse.components Y)) ⟩D⟩ F.onMorphisms (η.morphism.components Y)
          : by reflexivity
      ... =
      (F.onMorphisms (η.inverse.components X) ⟩D⟩ F.onMorphisms (η.morphism.components X)) ⟩D⟩ h ⟩D⟩ (F.onMorphisms (η.inverse.components Y) ⟩D⟩ F.onMorphisms (η.morphism.components Y))
          : ♮
      ... =
      F.onMorphisms (η.inverse.components X ⟩C⟩ η.morphism.components X) ⟩D⟩ h ⟩D⟩ F.onMorphisms (η.inverse.components Y ⟩C⟩ η.morphism.components Y)
          : ♮
      ... =
      F.onMorphisms (C.identity X) ⟩D⟩ h ⟩D⟩ F.onMorphisms (C.identity Y)
          : D.congr_compose
              (D.congr_compose_left h (congr_arg F.onMorphisms (η.componentwise_witness_2 X)))
              (congr_arg F.onMorphisms (η.componentwise_witness_2 Y))
      ... =
      h
          : ♮
end Equivalences_are_FullyFaithful

-- PROJECT finish this
-- lemma Equivalences_are_Faithful { C D : Category } ( e : Equivalence C D ) : Faithful (e.functor) := sorry

-- PROJECT finish this
-- lemma {u1 v1 u2 v2} FullyFaithfulEssentiallySurjective_Functors_are_Equivalences
--   { C : Category.{u1 v1} } { D : Category.{u2 v2} } 
--   ( F : Functor C D ) 
--   ( full : Full F ) 
--   ( faithful : Faithful F ) 
--   ( essentially_surjective : EssentiallySurjective F ) : is_Equivalence F :=
--   ⟨
--     {
--       functor := F,
--       inverse := {
--         onObjects     := λ X : D.Obj, (essentially_surjective X).1,
--         onMorphisms   := λ X Y f,
--                            (full (essentially_surjective X).1 (essentially_surjective Y).1).val
--                              (D.compose (D.compose (
--                                (essentially_surjective X).2.morphism)
--                                f
--                               ) (
--                                (essentially_surjective Y).2.inverse)
--                               ),
--         identities    := sorry,
--         functoriality := sorry
--       },
--       isomorphism_1 := begin
--                          pointwise,
--                          {
--                            -- Construct the forward map
--                            pointwise,
--                            all_goals { intros },
--                            unfold_unfoldable,
--                            exact (full _ _).val (essentially_surjective (F.onObjects X)).2.morphism,
--                            unfold_unfoldable,
                           
--                          }
--                        end,
--       isomorphism_2 := sorry
--     },
--     ♮
--   ⟩

end tqft.categories.equivalence