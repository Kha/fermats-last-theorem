import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_IsOrderCoord_fst_mem_span_natCast_of_mul_star_eq_intCast_mul

set_option autoImplicit false

open scoped Quaternion
open CerednikDrinfeld CerednikDrinfeld.QM QuaternionAlgebra

theorem CerednikDrinfeld.QM.IsOrderCoord.fst_mem_span_natCast_of_mul_star_eq_intCast_mul
    {r : ℕ} [Fact r.Prime] {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]}
    (hΛ : QuaternionAlgebra.IsOrder Λ) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    {coord : ↥Λ → Zp2 r × Zp2 r} (hcoord : IsOrderCoord Λ r coord)
    (m : ↥Λ) (n : ℤ) (hm : (m : ℍ[ℚ, a, b]) * star (m : ℍ[ℚ, a, b]) = (((r : ℤ) * n : ℚ) : ℍ[ℚ, a, b])) :
    (coord m).1 ∈ Ideal.span {((r : ℕ) : Zp2 r)} := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_IsOrderCoord_fst_mem_span_natCast_of_mul_star_eq_intCast_mul.solution
