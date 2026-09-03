import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_RegularProlongation_exists_smul_mem_integers_and_residue_ne_zero_or

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem AlgebraicCurve.RegularProlongation.exists_smul_mem_integers_and_residue_ne_zero_or
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField ↥A) Fbar]
    (R₁ R₂ : AlgebraicCurve.RegularProlongation A F Fbar) {f : F} (hf : f ≠ 0) :
    ∃ c : L, c ≠ 0 ∧ ∃ (h₁ : c • f ∈ R₁.integers) (h₂ : c • f ∈ R₂.integers),
      R₁.residue ⟨c • f, h₁⟩ ≠ 0 ∨ R₂.residue ⟨c • f, h₂⟩ ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_RegularProlongation_exists_smul_mem_integers_and_residue_ne_zero_or.solution
