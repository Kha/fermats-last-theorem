import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_RROpens_exists_degree_eq_sub_one_and_ell_eq_zero
attribute [-simp] ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single

universe u v

open AlgebraicCurve

theorem AlgebraicCurve.RROpens.exists_degree_eq_sub_one_and_ell_eq_zero
    {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F] [IsAlgClosed K]
    [IsCurveOver K F] [Nonempty (Place K F)] (Kc : Divisor K F) (g : ℕ)
    (hRR : ∀ D : Divisor K F, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g) :
    ∃ D : Divisor K F, Divisor.degree D = (g : ℤ) - 1 ∧ ell D = 0 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_RROpens_exists_degree_eq_sub_one_and_ell_eq_zero.solution
