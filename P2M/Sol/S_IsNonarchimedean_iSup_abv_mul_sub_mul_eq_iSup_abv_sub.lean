import Mathlib
import Definitions.Def_AlgebraicCurve_ChordalProximity
import P2M.Util
namespace P2MW.S_IsNonarchimedean_iSup_abv_mul_sub_mul_eq_iSup_abv_sub

set_option autoImplicit false

open AlgebraicCurve

namespace P2MC23

variable {K : Type*} [Field K] (μ : AbsoluteValue K ℝ)

theorem bddAbove_range {ι : Type*} [Fintype ι] (f : ι → ℝ) : BddAbove (Set.range f) :=
  (Set.finite_range f).bddAbove

theorem le_ciSup_fin {ι : Type*} [Fintype ι] (f : ι → ℝ) (i : ι) : f i ≤ ⨆ j, f j :=
  le_ciSup (bddAbove_range f) i

theorem main (hμ : IsNonarchimedean μ) {r : ℕ}
    (x v : Fin r → K) (i : Fin r) (hxi : x i = 1) (hvi : v i = 1)
    (hx : ∀ l, μ (x l) ≤ 1) (hv : ∀ l, μ (v l) ≤ 1) :
    (⨆ p : Fin r × Fin r, μ (x p.1 * v p.2 - x p.2 * v p.1)) = ⨆ l, μ (x l - v l) := by
  haveI : Nonempty (Fin r) := ⟨i⟩
  apply le_antisymm
  ·
    refine ciSup_le fun p => ?_
    have hid : x p.1 * v p.2 - x p.2 * v p.1 = (x p.1 - v p.1) * v p.2 - (x p.2 - v p.2) * v p.1 := by ring
    rw [hid]
    calc μ ((x p.1 - v p.1) * v p.2 - (x p.2 - v p.2) * v p.1)
        ≤ max (μ ((x p.1 - v p.1) * v p.2)) (μ ((x p.2 - v p.2) * v p.1)) := by
          have := hμ ((x p.1 - v p.1) * v p.2) (-((x p.2 - v p.2) * v p.1))
          rwa [← sub_eq_add_neg, map_neg_eq_map] at this
      _ ≤ max (μ (x p.1 - v p.1)) (μ (x p.2 - v p.2)) := by
          rw [map_mul, map_mul]
          exact max_le_max (mul_le_of_le_one_right (μ.nonneg _) (hv _)) (mul_le_of_le_one_right (μ.nonneg _) (hv _))
      _ ≤ ⨆ l, μ (x l - v l) :=
          max_le (le_ciSup_fin (fun l => μ (x l - v l)) p.1) (le_ciSup_fin (fun l => μ (x l - v l)) p.2)
  ·
    refine ciSup_le fun l => ?_
    have : μ (x l - v l) = μ (x (l, i).1 * v (l, i).2 - x (l, i).2 * v (l, i).1) := by
      simp only [hxi, hvi, mul_one, one_mul]
    rw [this]
    exact le_ciSup_fin (fun p : Fin r × Fin r => μ (x p.1 * v p.2 - x p.2 * v p.1)) (l, i)

theorem iSup_eq_one {r : ℕ} (x : Fin r → K) (i : Fin r) (hxi : x i = 1) (hx : ∀ l, μ (x l) ≤ 1) :
    (⨆ l, μ (x l)) = 1 := by
  haveI : Nonempty (Fin r) := ⟨i⟩
  apply le_antisymm (ciSup_le hx)
  have := le_ciSup_fin (fun l => μ (x l)) i
  rwa [hxi, map_one] at this

theorem prox_eq (hμ : IsNonarchimedean μ) {r : ℕ}
    (x v : Fin r → K) (i : Fin r) (hxi : x i = 1) (hvi : v i = 1)
    (hx : ∀ l, μ (x l) ≤ 1) (hv : ∀ l, μ (v l) ≤ 1) :
    prox μ x v = - Real.log (⨆ l, μ (x l - v l)) := by
  unfold prox
  rw [iSup_eq_one μ x i hxi hx, iSup_eq_one μ v i hvi hv, Real.log_one, main μ hμ x v i hxi hvi hx hv]
  ring

end P2MC23

theorem solution {K : Type*} [Field K] (μ : AbsoluteValue K ℝ) (hμ : IsNonarchimedean μ) {r : ℕ}
    (x v : Fin r → K) (i : Fin r) (hxi : x i = 1) (hvi : v i = 1)
    (hx : ∀ l, μ (x l) ≤ 1) (hv : ∀ l, μ (v l) ≤ 1) :
    (⨆ p : Fin r × Fin r, μ (x p.1 * v p.2 - x p.2 * v p.1)) = ⨆ l, μ (x l - v l) :=
  P2MC23.main μ hμ x v i hxi hvi hx hv
