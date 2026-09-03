import Definitions.Def_CuspForm_HeckeAlgebra
import Definitions.Def_CuspForm_IntegralStructure
import P2M.Util
import P2M.Sol.S_CuspForm_HasIntegralStructure_exists_isNormalizedEigenform_qCoeff_eq

theorem CuspForm.HasIntegralStructure.exists_isNormalizedEigenform_qCoeff_eq {N : ℕ} [NeZero N] (hN : CuspForm.HasIntegralStructure N 2) {S : Set ℕ} (χ : CuspForm.heckeAlgebra N 2 S →+* ℂ) : ∃ f : CuspForm (CongruenceSubgroup.Gamma0 N) 2, f.IsNormalizedEigenform ∧ (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ S), ModularFormClass.qCoeff f ℓ = χ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)) ∧ ∀ (q : ℕ) (hq : q.Prime) (hqN : q ∣ N) (hqS : q ∉ S), ModularFormClass.qCoeff f q = χ (CuspForm.heckeAlgebra.U hq hqN hqS) := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_HasIntegralStructure_exists_isNormalizedEigenform_qCoeff_eq.solution
