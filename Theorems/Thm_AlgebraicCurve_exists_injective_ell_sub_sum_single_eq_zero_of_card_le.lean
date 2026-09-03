import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_exists_injective_ell_sub_sum_single_eq_zero_of_card_le

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.exists_injective_ell_sub_sum_single_eq_zero_of_card_le
    {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F]
    [Algebra.EssFiniteType K F]
    (G : Divisor K F) {n : ℕ} (hn : ell G = n)
    (X S : Finset (Place K F)) (hS : ∀ v ∈ S, v.deg = 1)
    (hcard : (X.card : ℤ) + Divisor.degree G + 1 ≤ S.card) :
    ∃ Q : Fin n → Place K F, Function.Injective Q ∧ (∀ l, Q l ∈ S ∧ Q l ∉ X) ∧
      ell (G - ∑ l, Finsupp.single (Q l) 1) = 0 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_exists_injective_ell_sub_sum_single_eq_zero_of_card_le.solution
