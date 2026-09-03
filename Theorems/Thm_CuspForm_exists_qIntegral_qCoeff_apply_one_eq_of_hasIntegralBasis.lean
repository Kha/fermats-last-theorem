import Definitions.Def_CuspForm_HeckeAlgebra
import Definitions.Def_CuspForm_IntegralLattice
import P2M.Util
import P2M.Sol.S_CuspForm_exists_qIntegral_qCoeff_apply_one_eq_of_hasIntegralBasis

theorem CuspForm.exists_qIntegral_qCoeff_apply_one_eq_of_hasIntegralBasis (p m : ℕ) [Fact p.Prime] [NeZero m] (hIB : CuspForm.HasIntegralBasis p) (φ : CuspForm.heckeAlgebra p 2 ∅ →ₗ[ℤ] ZMod m) : ∃ f ∈ CuspForm.qIntegralSet p, ∀ t : CuspForm.heckeAlgebra p 2 ∅, ∀ c : ℤ, (c : ℂ) = ModularFormClass.qCoeff ((t : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 p) 2)) f) 1 → (c : ZMod m) = φ t := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_exists_qIntegral_qCoeff_apply_one_eq_of_hasIntegralBasis.solution
