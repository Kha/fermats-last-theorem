import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_RROpens_exists_finset_subset_ell_sub_sum_single_eq_zero

universe u v

open AlgebraicCurve

theorem AlgebraicCurve.RROpens.exists_finset_subset_ell_sub_sum_single_eq_zero
    {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F] [IsAlgClosed K]
    [IsCurveOver K F] (Kc : Divisor K F) (g : ℕ)
    (hRR : ∀ D : Divisor K F, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g)
    (G : Divisor K F) (S : Set (Place K F)) (hS : S.Infinite) :
    ∃ T : Finset (Place K F), (↑T : Set (Place K F)) ⊆ S ∧ T.card = ell G ∧
      ell (G - ∑ v ∈ T, Finsupp.single v 1) = 0 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_RROpens_exists_finset_subset_ell_sub_sum_single_eq_zero.solution
