import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_IsOrderCoord_exists_mul_star_eq_and_fst_mem_span_pow_and_snd_sub_one_mem_span_pow

set_option autoImplicit false

open scoped Quaternion
open CerednikDrinfeld CerednikDrinfeld.QM QuaternionAlgebra

theorem CerednikDrinfeld.QM.IsOrderCoord.exists_mul_star_eq_and_fst_mem_span_pow_and_snd_sub_one_mem_span_pow
    {r : ℕ} [Fact r.Prime] {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]}
    (hΛ : QuaternionAlgebra.IsOrder Λ) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    {coord : ↥Λ → Zp2 r × Zp2 r} (hcoord : IsOrderCoord Λ r coord) (k : ℕ) :
    ∃ m : ↥Λ, (∃ n : ℤ, (m : ℍ[ℚ, a, b]) * star (m : ℍ[ℚ, a, b]) = (((r : ℤ) * n : ℚ) : ℍ[ℚ, a, b])) ∧
      (coord m).1 ∈ Ideal.span {((r : ℕ) : Zp2 r) ^ k} ∧ (coord m).2 - 1 ∈ Ideal.span {((r : ℕ) : Zp2 r) ^ k} := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_IsOrderCoord_exists_mul_star_eq_and_fst_mem_span_pow_and_snd_sub_one_mem_span_pow.solution
