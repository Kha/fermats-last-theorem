import Mathlib
import Definitions.Def_DrinfeldCurve_LocalChart
import P2M.Util
import P2M.Sol.S_DrinfeldCurve_LocalChart_exists_sub_C_eq_mk_of_sub_eq_pow_mul

set_option autoImplicit false

open MvPowerSeries

theorem DrinfeldCurve.LocalChart.exists_sub_C_eq_mk_of_sub_eq_pow_mul
    (q : ℕ) {W : Type} [CommRing W]
    (c : W) (f u v : MvPowerSeries (Fin 2) W) (hv : IsUnit v)
    (hf : f - DrinfeldCurve.LocalChart.drinfeldForm q W ∈
      (Ideal.span {(X 0 : MvPowerSeries (Fin 2) W), X 1}) ^ (q + 2))
    (s : MvPowerSeries (Fin 2) W ⧸ Ideal.span {C c * v - f * u})
    (a₀ a w : W) (N : ℕ) (ha : a₀ - a = c ^ N * w)
    (e₀ : ℕ) (hN : e₀ + 1 ≤ N * (q + 1))
    (h : MvPowerSeries (Fin 2) W)
    (hh : h ∈ (Ideal.span {(X 0 : MvPowerSeries (Fin 2) W), X 1}) ^ e₀)
    (hs : s - Ideal.Quotient.mk _ (C a₀) = Ideal.Quotient.mk _ h) :
    ∃ h' : MvPowerSeries (Fin 2) W,
      h' ∈ (Ideal.span {(X 0 : MvPowerSeries (Fin 2) W), X 1}) ^ e₀ ∧
      (∀ i : ℕ, i ≤ e₀ → coeff (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) (e₀ - i)) h' =
        coeff (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) (e₀ - i)) h) ∧
      s - Ideal.Quotient.mk _ (C a) = Ideal.Quotient.mk _ h' := by p2m_exact_reverting @_root_.P2MW.S_DrinfeldCurve_LocalChart_exists_sub_C_eq_mk_of_sub_eq_pow_mul.solution
