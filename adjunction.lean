-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import .natural_transformation
import .opposites
import .products.products
import .isomorphism
import .examples.types.types

open tqft.categories
open tqft.categories.functor
open tqft.categories.natural_transformation
open tqft.categories.products
open tqft.categories.isomorphism
open tqft.categories.examples.types

namespace tqft.categories.adjunction

structure Adjunction { C D : Category } ( L : Functor C D ) ( R : Functor D C ) :=
  ( unit          : NaturalTransformation (IdentityFunctor C) (FunctorComposition L R) )
  ( counit        : NaturalTransformation (FunctorComposition R L) (IdentityFunctor D) )
  ( triangle_1   : ∀ X : D.Obj, C.compose (unit.components (R X)) (R.onMorphisms (counit.components X)) = C.identity (R X) )
  ( triangle_2   : ∀ X : C.Obj, D.compose (L.onMorphisms (unit.components X)) (counit.components (L X)) = D.identity (L X) )

attribute [ematch] Adjunction.triangle_1 Adjunction.triangle_2

@[pointwise] lemma Adjunctions_pointwise_equal
  { C D : Category } ( L : Functor C D ) ( R : Functor D C )
  ( A B : Adjunction L R )
  ( w1 : A.unit = B.unit ) ( w2 : A.counit = B.counit ) : A = B :=
  begin
    induction A,
    induction B,
    blast
  end


-- PROJECT: from an adjunction construct the triangles as equations between natural transformations.
-- definition Triangle_1
--   { C D : Category }
--   { L : Functor C D }
--   { R : Functor D C }
--   ( unit   : NaturalTransformation (IdentityFunctor C) (FunctorComposition L R) )
--   ( counit : NaturalTransformation (FunctorComposition R L) (IdentityFunctor D) ) :=
--   @vertical_composition_of_NaturalTransformations D C R (FunctorComposition (FunctorComposition R L) R) R ⟦ whisker_on_left R unit ⟧ ⟦ whisker_on_right counit R ⟧
--   = IdentityNaturalTransformation R

-- definition Triangle_2
--   { C D : Category }
--   { L : Functor C D }
--   { R : Functor D C }
--   ( unit   : NaturalTransformation (IdentityFunctor C) (FunctorComposition L R) )
--   ( counit : NaturalTransformation (FunctorComposition R L) (IdentityFunctor D) ) :=
--   @vertical_composition_of_NaturalTransformations C D L (FunctorComposition (FunctorComposition L R) L) L ⟦ whisker_on_right unit L ⟧ ⟦ whisker_on_left L counit ⟧
--   = IdentityNaturalTransformation L

@[ematch] lemma Adjunction.unit_naturality
  { C D : Category } 
  { L : Functor C D } { R : Functor D C } 
  ( A : Adjunction L R ) 
  { X Y : C.Obj } ( f : C.Hom X Y ) : C.compose f (A.unit.components Y) = C.compose (A.unit.components X) (R.onMorphisms (L.onMorphisms f)) :=
  begin
    refine ( cast _ (A.unit.naturality f) ),
    blast
  end
@[ematch] lemma Adjunction.counit_naturality
  { C D : Category } 
  { L : Functor C D } { R : Functor D C } 
  ( A : Adjunction L R ) 
  { X Y : D.Obj } ( f : D.Hom X Y ) : D.compose (L.onMorphisms (R.onMorphisms f)) (A.counit.components Y) = D.compose (A.counit.components X) f :=
  begin
    refine ( cast _ (A.counit.naturality f) ),
    blast
  end

-- set_option pp.all true

definition { u v } HomPairing ( C : Category.{u v} ) : Functor ((Opposite C) × C) CategoryOfTypes.{v} :=
{
  onObjects     := λ p, C.Hom p.1 p.2,
  onMorphisms   := λ X F f, λ g, C.compose (C.compose f.1 g) f.2,
  identities    := ♯,
  functoriality := ♯
}

definition HomAdjunction { C D : Category } ( L : Functor C D ) ( R : Functor D C ) :=
  NaturalIsomorphism
    (FunctorComposition (OppositeFunctor L × IdentityFunctor D) (HomPairing D))
    (FunctorComposition (IdentityFunctor (Opposite C) × R) (HomPairing C))

definition Adjunction_to_HomAdjunction  { C D : Category } ( L : Functor C D ) ( R : Functor D C ) ( A : Adjunction L R ) : HomAdjunction L R := 
{
    morphism  := {
      components := λ P, 
        -- We need to construct the map from D.Hom (L P.1) P.2 to D.Hom P.1 (R P.2)
        λ f, C.compose (A.unit P.1) (R.onMorphisms f),
      naturality := begin
                      intros,
                      pointwise,
                      intros,
                      unfold_unfoldable,
                      repeat { rewrite - C.associativity },
                      erewrite A.unit_naturality,
                      trivial
                    end
    },
    inverse   := 
    {
      components := λ P, 
        -- We need to construct the map back to D.Hom (L P.1) P.2 from D.Hom P.1 (R P.2)
        λ f, D.compose (L.onMorphisms f) (A.counit P.2),
      naturality := begin
                      intros,
                      pointwise,
                      intros,
                      unfold_unfoldable,
                      repeat { rewrite D.associativity },
                      erewrite - A.counit_naturality,
                      trivial
                    end
    },
    witness_1 := begin
                   pointwise,
                   intros,
                   pointwise,
                   intros,
                   unfold_unfoldable,
                   erewrite D.associativity,
                   erewrite A.counit_naturality,
                   erewrite - D.associativity,
                   erewrite A.triangle_2,
                   simp
                 end,
    witness_2 := begin
                   pointwise,
                   intros,
                   pointwise,
                   intros,
                   unfold_unfoldable,
                   erewrite - C.associativity,
                   erewrite - A.unit_naturality,
                   erewrite C.associativity,
                   erewrite A.triangle_1,
                   simp
                 end
  }



-- PROJECT examples
-- PROJECT adjoints are unique
-- PROJECT equivalences can be lifted to adjoint equivalences
-- PROJECT universal properties of adjunctions
-- PROJECT show these are a special case of a duality in a 2-category.
-- PROJECT adjoints of monoidal functors are (op)lax

end tqft.categories.adjunction