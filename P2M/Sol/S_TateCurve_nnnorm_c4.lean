import Definitions.Def_TateCurve_QSeries
import P2M.Util
namespace P2MW.S_TateCurve_nnnorm_c4
open scoped NNReal
open TateCurve IsUltrametricDist

theorem solution {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    {q : K} (hq : ‖q‖₊ < 1) : ‖(curve q).c₄‖₊ = 1 := by
  have h : ‖(curve q).c₄ - 1‖₊ < 1 := by
    rw [curve_c₄]
    have heq : (1 : K) - 48 * a₄ q - 1 = -(48 * a₄ q) := by ring
    rw [heq, nnnorm_neg, nnnorm_mul]
    calc ‖(48 : K)‖₊ * ‖a₄ q‖₊ ≤ 1 * ‖q‖₊ := by
          gcongr
          · exact_mod_cast nnnorm_natCast_le_one K 48
          · exact nnnorm_a₄_le hq
      _ = ‖q‖₊ := one_mul _
      _ < 1 := hq
  have h2 := nnnorm_eq_of_nnnorm_sub_lt (a := (curve q).c₄) (b := (1 : K)) (by rw [nnnorm_one]; exact h)
  rwa [nnnorm_one] at h2
