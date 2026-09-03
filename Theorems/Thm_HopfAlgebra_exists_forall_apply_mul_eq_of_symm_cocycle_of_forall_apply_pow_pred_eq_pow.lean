import Mathlib
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_forall_apply_mul_eq_of_symm_cocycle_of_forall_apply_pow_pred_eq_pow
attribute [-instance] HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra
attribute [-simp] HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul

universe u v

theorem HopfAlgebra.exists_forall_apply_mul_eq_of_symm_cocycle_of_forall_apply_pow_pred_eq_pow
    (k : Type u) [Field k] [PerfectField k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (R : Type v) [CommRing R] [HopfAlgebra k R] [Module.Finite k R]
    (c : R →ₗ[k] R →ₗ[k] k)
    (hsymm : ∀ r s, c r s = c s r)
    (hcocycle : ∀ r s t,
      c (r * s) t + c r s * Coalgebra.counit (R := k) t =
        c r (s * t) + Coalgebra.counit (R := k) r * c s t)
    (hone : ∀ s, c 1 s = 0)
    (ℓ : R →ₗ[k] k) (hℓ₁ : ℓ 1 = 0) (hℓ : ∀ r : R, r ^ p = 0 → ℓ r = 0)
    (hpow : ∀ r : R, Coalgebra.counit (R := k) r = 0 → c (r ^ (p - 1)) r = ℓ r ^ p) :
    ∃ u : R →ₗ[k] k, ∀ r s,
      u (r * s) = Coalgebra.counit (R := k) r * u s + Coalgebra.counit (R := k) s * u r + c r s := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_forall_apply_mul_eq_of_symm_cocycle_of_forall_apply_pow_pred_eq_pow.solution
