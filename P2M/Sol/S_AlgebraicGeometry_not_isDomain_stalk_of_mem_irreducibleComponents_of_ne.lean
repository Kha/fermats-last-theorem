import Mathlib
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_not_isDomain_stalk_of_mem_irreducibleComponents_of_ne

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

theorem solution
    (Y : Scheme.{u}) (y : ↥Y) (Z₁ Z₂ : Set ↥Y)
    (hZ₁ : Z₁ ∈ irreducibleComponents ↥Y) (hZ₂ : Z₂ ∈ irreducibleComponents ↥Y)
    (hne : Z₁ ≠ Z₂) (hy₁ : y ∈ Z₁) (hy₂ : y ∈ Z₂) :
    ¬ IsDomain (Y.presheaf.stalk y) := by
  intro hdom

  haveI : IrreducibleSpace ↥(Spec (Y.presheaf.stalk y)) :=
    inferInstanceAs (IrreducibleSpace (PrimeSpectrum (Y.presheaf.stalk y)))
  have hS : IsIrreducible {x : ↥Y | x ⤳ y} := by
    rw [← Scheme.range_fromSpecStalk, ← Set.image_univ]
    exact IsIrreducible.image (IrreducibleSpace.isIrreducible_univ _) _ (Y.fromSpecStalk y).continuous.continuousOn
  have hS' : IsIrreducible (closure {x : ↥Y | x ⤳ y}) := hS.closure

  have key : ∀ Z ∈ irreducibleComponents ↥Y, y ∈ Z → Z = closure {x : ↥Y | x ⤳ y} := by
    intro Z hZ hyZ
    obtain ⟨ξ, hξ⟩ := QuasiSober.sober hZ.1 (isClosed_of_mem_irreducibleComponents Z hZ)
    have hξy : ξ ⤳ y := by
      rw [specializes_iff_mem_closure, hξ.def]
      exact hyZ
    have hZle : Z ⊆ closure {x : ↥Y | x ⤳ y} := by
      rw [← hξ.def]
      exact closure_mono (Set.singleton_subset_iff.2 hξy)
    exact Set.Subset.antisymm hZle (hZ.2 hS' hZle)
  exact hne ((key Z₁ hZ₁ hy₁).trans (key Z₂ hZ₂ hy₂).symm)
