import Definitions.Def_CuspForm_HeckeAlgebra
import Definitions.Def_CuspForm_IntegralStructure
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import P2M.Util
import P2M.Sol.S_CuspForm_IsNormalizedEigenform_exists_ringHom_heckeAlgebra_integralClosure

theorem CuspForm.IsNormalizedEigenform.exists_ringHom_heckeAlgebra_integralClosure {N : ℕ} [NeZero N] (hN : CuspForm.HasIntegralStructure N 2) {f : CuspForm (CongruenceSubgroup.Gamma0 N) 2} (hf : f.IsNormalizedEigenform) (S : Set ℕ) : ∃ χ : CuspForm.heckeAlgebra N 2 S →+* integralClosure ℤ ℂ, ∀ t : CuspForm.heckeAlgebra N 2 S, (t : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)) f = (χ t : ℂ) • f := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_IsNormalizedEigenform_exists_ringHom_heckeAlgebra_integralClosure.solution
