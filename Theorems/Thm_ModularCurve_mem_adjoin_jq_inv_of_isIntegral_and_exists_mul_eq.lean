import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_GaloisRep_Flat
import P2M.Util
import P2M.Sol.S_ModularCurve_mem_adjoin_jq_inv_of_isIntegral_and_exists_mul_eq

open ModularCurve IntermediateField

theorem ModularCurve.mem_adjoin_jq_inv_of_isIntegral_and_exists_mul_eq (p : ℕ) [Fact p.Prime] :
    (∀ x : LaurentSeries ℚ, x ∈ ℚ⟮jq⟯ →
      IsIntegral ↥(Algebra.adjoin ↥(GaloisRep.ratLocalizedAt p) ({jq⁻¹} : Set (LaurentSeries ℚ))) x →
      x ∈ Algebra.adjoin ↥(GaloisRep.ratLocalizedAt p) ({jq⁻¹} : Set (LaurentSeries ℚ))) ∧
    (∀ x : LaurentSeries ℚ, x ∈ ℚ⟮jq⟯ →
      ∃ b ∈ Algebra.adjoin ↥(GaloisRep.ratLocalizedAt p) ({jq⁻¹} : Set (LaurentSeries ℚ)),
      ∃ s ∈ Algebra.adjoin ↥(GaloisRep.ratLocalizedAt p) ({jq⁻¹} : Set (LaurentSeries ℚ)),
        s ≠ 0 ∧ s * x = b) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_mem_adjoin_jq_inv_of_isIntegral_and_exists_mul_eq.solution
