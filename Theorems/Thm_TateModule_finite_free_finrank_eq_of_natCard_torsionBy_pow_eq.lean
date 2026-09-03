import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_ModularCurve_JZeroTateModule
import P2M.Util
import P2M.Sol.S_TateModule_finite_free_finrank_eq_of_natCard_torsionBy_pow_eq

set_option autoImplicit false

open scoped TensorProduct

theorem TateModule.finite_free_finrank_eq_of_natCard_torsionBy_pow_eq
    (ℓ : ℕ) [Fact ℓ.Prime] (M : Type) [AddCommGroup M] (d : ℕ)
    (hcard : ∀ n : ℕ, Nat.card (Submodule.torsionBy ℤ M ((ℓ ^ n : ℕ) : ℤ)) = (ℓ ^ n) ^ d) :
    Module.Finite ℤ_[ℓ] (TateModule ℓ M) ∧ Module.Free ℤ_[ℓ] (TateModule ℓ M) ∧
      Module.finrank ℤ_[ℓ] (TateModule ℓ M) = d ∧
      Module.finrank ℚ_[ℓ] (ModularCurve.RationalTateModule ℓ M) = d := by p2m_exact_reverting @_root_.P2MW.S_TateModule_finite_free_finrank_eq_of_natCard_torsionBy_pow_eq.solution
