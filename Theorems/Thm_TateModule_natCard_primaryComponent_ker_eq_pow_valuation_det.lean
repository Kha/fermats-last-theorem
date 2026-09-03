import Mathlib.GroupTheory.Torsion
import Mathlib.LinearAlgebra.Determinant
import Definitions.Def_EllipticCurve_TateModule
import P2M.Util
import P2M.Sol.S_TateModule_natCard_primaryComponent_ker_eq_pow_valuation_det
set_option autoImplicit false

theorem TateModule.natCard_primaryComponent_ker_eq_pow_valuation_det (p : ℕ) [Fact p.Prime] {M : Type}
    [AddCommGroup M] (r : ℕ) (hcard : ∀ n : ℕ, Nat.card (Submodule.torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ r)
    (α : M →+ M) (hdet : LinearMap.det (TateModule.rep p M (Module.End ℤ M) α.toIntLinearMap) ≠ 0) :
    Nat.card (AddCommGroup.primaryComponent α.ker p) =
      p ^ (LinearMap.det (TateModule.rep p M (Module.End ℤ M) α.toIntLinearMap)).valuation := by p2m_exact_reverting @_root_.P2MW.S_TateModule_natCard_primaryComponent_ker_eq_pow_valuation_det.solution
