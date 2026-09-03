import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Pic0_exists_mk_eq_and_dvd_ord_of_mem_torsion

open AlgebraicCurve
theorem AlgebraicCurve.Pic0.exists_mk_eq_and_dvd_ord_of_mem_torsion {K F : Type*} [Field K] [Field F] [Algebra K F] {n : ℕ} {x : Pic0 K F}
    (hx : x ∈ Pic0.torsion K F n) :
    ∃ (D : Divisor.degZero (K := K) (F := F)) (f : F),
      Pic0.mk D = x ∧ f ≠ 0 ∧ (∀ v : Place K F, (n : ℤ) ∣ v.ord f) ∧
        ∀ v : Place K F, v.ord f = n * (D : Divisor K F) v := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Pic0_exists_mk_eq_and_dvd_ord_of_mem_torsion.solution
