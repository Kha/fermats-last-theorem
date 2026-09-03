import Mathlib
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_le_topologicalKrullDim
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_topologicalKrullDim_le
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_SmoothOfRelativeDimension_topologicalKrullDim_preimage_singleton_eq

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) [SmoothOfRelativeDimension n f]
    (y : ↥Y) (hy : (f.base ⁻¹' {y}).Nonempty) :
    topologicalKrullDim ↥(f.base ⁻¹' {y}) = n := by
  haveI := smoothOfRelativeDimension_isStableUnderBaseChange (n := n)
  haveI : SmoothOfRelativeDimension n (f.fiberToSpecResidueField y) :=
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension n) f (Y.fromSpecResidueField y) inferInstance
  have hne : Nonempty ↥(f.fiber y) := by
    obtain ⟨x, hx⟩ := hy
    exact ⟨(f.fiberHomeo y).symm ⟨x, hx⟩⟩
  have h1 : (n : WithBot ℕ∞) ≤ topologicalKrullDim ↥(f.fiber y) :=
    AlgebraicGeometry.SmoothOfRelativeDimension.le_topologicalKrullDim
      (K := ↑(Y.residueField y)) (f.fiberToSpecResidueField y) n
  have h2 : topologicalKrullDim ↥(f.fiber y) ≤ n :=
    AlgebraicGeometry.SmoothOfRelativeDimension.topologicalKrullDim_le
      (K := ↑(Y.residueField y)) (f.fiberToSpecResidueField y) n
  have h3 : topologicalKrullDim ↥(f.fiber y) = topologicalKrullDim ↥(f.base ⁻¹' {y}) :=
    IsHomeomorph.topologicalKrullDim_eq _ (f.fiberHomeo y).isHomeomorph
  rw [← h3]
  exact le_antisymm h2 h1
