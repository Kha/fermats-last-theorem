import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_ComponentGroup
import Definitions.Def_AlgebraicCurve_SemistableCharts
import P2M.Util
import P2M.Sol.S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_annulus_ord_residue_eq_one_and_endSlope_both_ends_of_forall_isUnit_evalAt_mem_integers

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve
  IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP
open scoped MatrixGroups

theorem ModularCurve.JHPlaceSpecialization.ProlongationDatum.annulus_ord_residue_eq_one_and_endSlope_both_ends_of_forall_isUnit_evalAt_mem_integers
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ))
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (SS : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) ×
      Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)

    (s : ↥SS) (An : AlgebraicCurve.Annulus A ↥(xHFunctionFieldBar M H))

    (hz₂ : ∃ h₂ : An.param ∈ Rpd.R₂.integers, s.1.2.ord (Rpd.R₂.residue ⟨An.param, h₂⟩) = 1)
    (hz₁ : ∃ h₁ : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((An.modulus : ↥A) : AlgebraicClosure ℚ) * An.param⁻¹ ∈ Rpd.R₁.integers,
      s.1.1.ord (Rpd.R₁.residue ⟨_, h₁⟩) = 1)

    (hu₂ : ∀ g : ↥(xHFunctionFieldBar M H), g ≠ 0 → (∀ P ∈ An.dom, P.ord g = 0) → (∀ P ∈ An.dom, ∃ h : P.evalAt g ∈ A, IsUnit (⟨_, h⟩ : ↥A)) →
      ∃ hg : g ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨g, hg⟩ ≠ 0 ∧ s.1.2.ord (Rpd.R₂.residue ⟨g, hg⟩) = 0)
    (hu₁ : ∀ g : ↥(xHFunctionFieldBar M H), g ≠ 0 → (∀ P ∈ An.dom, P.ord g = 0) → (∀ P ∈ An.dom, ∃ h : P.evalAt g ∈ A, IsUnit (⟨_, h⟩ : ↥A)) →
      ∃ hg : g ∈ Rpd.R₁.integers, Rpd.R₁.residue ⟨g, hg⟩ ≠ 0 ∧ s.1.1.ord (Rpd.R₁.residue ⟨g, hg⟩) = 0) :
    (∃ h₂ : An.param ∈ Rpd.R₂.integers, s.1.2.ord (Rpd.R₂.residue ⟨An.param, h₂⟩) = 1 ∧
      ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨f, hf⟩ ≠ 0 →
        (∀ P ∈ An.dom, P.ord f = 0) → ∀ P ∈ An.dom,
          ∃ h : P.evalAt f * (P.evalAt An.param) ^ (-(s.1.2.ord (Rpd.R₂.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A)) ∧
    (∃ h₁ : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((An.modulus : ↥A) : AlgebraicClosure ℚ) * An.param⁻¹ ∈ Rpd.R₁.integers,
      s.1.1.ord (Rpd.R₁.residue ⟨_, h₁⟩) = 1 ∧
      ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨f, hf⟩ ≠ 0 →
        (∀ P ∈ An.dom, P.ord f = 0) → ∀ P ∈ An.dom,
          ∃ h : P.evalAt f * (P.evalAt (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((An.modulus : ↥A) : AlgebraicClosure ℚ) * An.param⁻¹)) ^
            (-(s.1.1.ord (Rpd.R₁.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_annulus_ord_residue_eq_one_and_endSlope_both_ends_of_forall_isUnit_evalAt_mem_integers.solution
