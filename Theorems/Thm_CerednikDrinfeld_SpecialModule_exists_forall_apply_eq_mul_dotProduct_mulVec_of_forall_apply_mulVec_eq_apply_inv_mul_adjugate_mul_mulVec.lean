import Mathlib
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_SpecialModule_exists_forall_apply_eq_mul_dotProduct_mulVec_of_forall_apply_mulVec_eq_apply_inv_mul_adjugate_mul_mulVec

set_option autoImplicit false

theorem CerednikDrinfeld.SpecialModule.exists_forall_apply_eq_mul_dotProduct_mulVec_of_forall_apply_mulVec_eq_apply_inv_mul_adjugate_mul_mulVec
    (k : Type) [Field k] (μ : Matrix (Fin 2) (Fin 2) k) (htr : μ.trace = 0) (hdet : μ.det ≠ 0)
    (b : (Fin 2 → k) →ₗ[k] (Fin 2 → k) →ₗ[k] k)
    (hb : ∀ (x : Matrix (Fin 2) (Fin 2) k) (v w : Fin 2 → k),
      b (x.mulVec v) w = b v ((μ⁻¹ * x.adjugate * μ).mulVec w)) :
    ∃ c : k, ∀ v w : Fin 2 → k,
      b v w = c * dotProduct v ((!![0, 1; -1, 0] * μ).mulVec w) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_SpecialModule_exists_forall_apply_eq_mul_dotProduct_mulVec_of_forall_apply_mulVec_eq_apply_inv_mul_adjugate_mul_mulVec.solution
