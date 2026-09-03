import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_RegularProlongation_exists_regularProlongation_mem_integers_iff_of_le

open AlgebraicCurve

theorem AlgebraicCurve.RegularProlongation.exists_regularProlongation_mem_integers_iff_of_le.{u}
    {L : Type*} [Field L] (A A' : ValuationSubring L) (hA : A ≤ A')
    {F : Type u} [Field F] [Algebra L F]
    {Fb : Type*} [Field Fb] [Algebra (IsLocalRing.ResidueField A) Fb]
    (R : RegularProlongation A F Fb)
    (f : F) (hf : f ∈ R.integers)
    (htr : Transcendental (IsLocalRing.ResidueField A) (R.residue ⟨f, hf⟩)) :
    ∃ (Fb' : Type u) (_ : Field Fb') (_ : Algebra (IsLocalRing.ResidueField A') Fb')
      (R' : RegularProlongation A' F Fb') (hle : R.integers ≤ R'.integers),
      (∀ x : F, x ∈ R'.integers ↔ ∃ a : L, A'.valuation a = 1 ∧ a • x ∈ R.integers) ∧
      Transcendental (IsLocalRing.ResidueField A') (R'.residue ⟨f, hle hf⟩) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_RegularProlongation_exists_regularProlongation_mem_integers_iff_of_le.solution
