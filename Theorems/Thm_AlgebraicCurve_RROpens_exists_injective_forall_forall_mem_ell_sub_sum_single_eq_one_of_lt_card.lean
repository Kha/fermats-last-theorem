import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_RROpens_exists_injective_forall_forall_mem_ell_sub_sum_single_eq_one_of_lt_card

universe u v w

open AlgebraicCurve

theorem AlgebraicCurve.RROpens.exists_injective_forall_forall_mem_ell_sub_sum_single_eq_one_of_lt_card
    {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F] [IsCurveOver K F]
    {Kc : Divisor K F} {g : ℕ}
    (hRR : ∀ D : Divisor K F, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g)
    {r : ℕ} (hgr : 2 * g ≤ r + 1)
    {N : ℕ} (D : Fin N → Divisor K F) (hdeg : ∀ k, Divisor.degree (D k) = r)
    {ι : Type w} [Fintype ι] [DecidableEq ι] (B : ι → Finset (Place K F))
    (hB : ∀ i, ∀ v ∈ B i, v.deg = 1) (hdisj : ∀ i i', i ≠ i' → Disjoint (B i) (B i'))
    {b : ℕ} (hb1 : 1 ≤ b) (hb : ∀ i, (B i).card ≤ b)
    (hcard : N * r * b ^ (r - g) + (r - g) < Fintype.card ι) :
    ∃ a : Fin (r - g) → ι, Function.Injective a ∧
      ∀ k, ∀ v : Fin (r - g) → Place K F, (∀ j, v j ∈ B (a j)) →
        ell (D k - ∑ j : Fin (r - g), Finsupp.single (v j) 1) = 1 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_RROpens_exists_injective_forall_forall_mem_ell_sub_sum_single_eq_one_of_lt_card.solution
