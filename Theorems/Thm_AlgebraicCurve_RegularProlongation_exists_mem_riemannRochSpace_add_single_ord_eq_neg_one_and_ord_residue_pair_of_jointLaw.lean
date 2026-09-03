import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_Repartitions
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_RegularProlongation_exists_mem_riemannRochSpace_add_single_ord_eq_neg_one_and_ord_residue_pair_of_jointLaw

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem AlgebraicCurve.RegularProlongation.exists_mem_riemannRochSpace_add_single_ord_eq_neg_one_and_ord_residue_pair_of_jointLaw
    {L : Type*} [Field L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {K Fb : Type*} [Field K] [Field Fb] [Algebra K Fb] [Algebra (IsLocalRing.ResidueField A) Fb]
    (R₁ R₂ : RegularProlongation A F Fb)
    (E : Divisor L F) (V₀ : Place L F) (hEV₀ : E V₀ = 0)
    (v₁ v₂ : Place K Fb)
    (hlaw : ∀ (g : F) (hg₁ : g ∈ R₁.integers) (hg₂ : g ∈ R₂.integers),
      g ∈ riemannRochSpace (E + Finsupp.single V₀ 1) →
        R₁.residue ⟨g, hg₁⟩ ≠ 0 → R₂.residue ⟨g, hg₂⟩ ≠ 0 →
          -1 ≤ v₁.ord (R₁.residue ⟨g, hg₁⟩) + v₂.ord (R₂.residue ⟨g, hg₂⟩))
    (p₁ : F) (hp₁E : p₁ ∈ riemannRochSpace E) (hp₁₁ : p₁ ∈ R₁.integers) (hp₁₂ : p₁ ∈ R₂.integers)
    (hp₁ : R₁.residue ⟨p₁, hp₁₁⟩ ≠ 0 ∧ v₁.ord (R₁.residue ⟨p₁, hp₁₁⟩) = 0 ∧
      (R₂.residue ⟨p₁, hp₁₂⟩ = 0 ∨ 0 ≤ v₂.ord (R₂.residue ⟨p₁, hp₁₂⟩)))
    (p₂ : F) (hp₂E : p₂ ∈ riemannRochSpace E) (hp₂₁ : p₂ ∈ R₁.integers) (hp₂₂ : p₂ ∈ R₂.integers)
    (hp₂ : R₂.residue ⟨p₂, hp₂₂⟩ ≠ 0 ∧ v₂.ord (R₂.residue ⟨p₂, hp₂₂⟩) = 0 ∧
      (R₁.residue ⟨p₂, hp₂₁⟩ = 0 ∨ 0 ≤ v₁.ord (R₁.residue ⟨p₂, hp₂₁⟩)))
    (f : F) (hfE : f ∈ riemannRochSpace (E + Finsupp.single V₀ 1))
    (hfV₀ : V₀.ord f = -1) (hf₁ : f ∈ R₁.integers) (hf₂ : f ∈ R₂.integers)
    (hviol : (R₁.residue ⟨f, hf₁⟩ ≠ 0 ∧ v₁.ord (R₁.residue ⟨f, hf₁⟩) < 0) ∨
      (R₂.residue ⟨f, hf₂⟩ ≠ 0 ∧ v₂.ord (R₂.residue ⟨f, hf₂⟩) < 0)) :
    ∃ (g : F) (hg₁ : g ∈ R₁.integers) (hg₂ : g ∈ R₂.integers),
      g ∈ riemannRochSpace (E + Finsupp.single V₀ 1) ∧ V₀.ord g = -1 ∧
      R₁.residue ⟨g, hg₁⟩ ≠ 0 ∧ R₂.residue ⟨g, hg₂⟩ ≠ 0 ∧
      ((v₁.ord (R₁.residue ⟨g, hg₁⟩) = -1 ∧ v₂.ord (R₂.residue ⟨g, hg₂⟩) = 0) ∨
        (v₁.ord (R₁.residue ⟨g, hg₁⟩) = 0 ∧ v₂.ord (R₂.residue ⟨g, hg₂⟩) = -1)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_RegularProlongation_exists_mem_riemannRochSpace_add_single_ord_eq_neg_one_and_ord_residue_pair_of_jointLaw.solution
