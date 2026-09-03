import Mathlib
import Theorems.Thm_AlgebraicGeometry_GeometricallyIrreducible_of_irreducibleSpace_of_isAlgClosed
import Theorems.Thm_AlgebraicGeometry_GeometricallyIrreducible_geometricallyConnected
import Theorems.Thm_AlgebraicGeometry_GeometricallyConnected_descendsAlong_surjective
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_geometricallyConnected_of_irreducibleSpace_pullback_of_isAlgClosed

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K))
    (k : Type u) [Field k] [Algebra K k] [IsAlgClosed k]
    [IrreducibleSpace ↑(pullback f (Spec.map (CommRingCat.ofHom (algebraMap K k))))] :
    GeometricallyConnected f := by
  set g : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of K) := Spec.map (CommRingCat.ofHom (algebraMap K k)) with hg
  haveI hirr : GeometricallyIrreducible (pullback.snd f g) :=
    AlgebraicGeometry.GeometricallyIrreducible.of_irreducibleSpace_of_isAlgClosed (pullback.snd f g)
  have hconn : GeometricallyConnected (pullback.snd f g) :=
    AlgebraicGeometry.GeometricallyIrreducible.geometricallyConnected (pullback.snd f g)
  have hsurj : Surjective g := ⟨fun x => ⟨(⊥ : PrimeSpectrum k), Subsingleton.elim _ _⟩⟩
  haveI : MorphismProperty.DescendsAlong (@GeometricallyConnected : MorphismProperty Scheme.{u}) @Surjective :=
    AlgebraicGeometry.GeometricallyConnected.descendsAlong_surjective
  exact MorphismProperty.of_pullback_snd_of_descendsAlong (P := @GeometricallyConnected) (Q := @Surjective) hsurj hconn
