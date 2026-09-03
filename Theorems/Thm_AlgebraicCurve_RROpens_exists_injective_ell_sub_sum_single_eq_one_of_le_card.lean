import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_RROpens_exists_injective_ell_sub_sum_single_eq_one_of_le_card

universe u v

open AlgebraicCurve

theorem AlgebraicCurve.RROpens.exists_injective_ell_sub_sum_single_eq_one_of_le_card
    {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F] [IsCurveOver K F]
    {Kc : Divisor K F} {g : ℕ}
    (hRR : ∀ D : Divisor K F, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g)
    {r : ℕ} (hgr : 2 * g ≤ r + 1)
    (S : Finset (Place K F)) (hS : ∀ v ∈ S, v.deg = 1) (hcard : r + 1 ≤ S.card)
    (D : Divisor K F) (hdeg : Divisor.degree D = r) :
    ∃ f : Fin (r - g) → Place K F, Function.Injective f ∧ (∀ j, f j ∈ S) ∧
      ell (D - ∑ j : Fin (r - g), Finsupp.single (f j) 1) = 1 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_RROpens_exists_injective_ell_sub_sum_single_eq_one_of_le_card.solution
