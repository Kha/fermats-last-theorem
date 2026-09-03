import Mathlib
import Definitions.Def_DrinfeldCurve_LocalChart
import P2M.Util
import P2M.Sol.S_DrinfeldCurve_LocalChart_card_eq_and_prod_linear_eq_drinfeldForm_and_isUnit_det_of_prod_X_sub_C_eq

set_option autoImplicit false

theorem DrinfeldCurve.LocalChart.card_eq_and_prod_linear_eq_drinfeldForm_and_isUnit_det_of_prod_X_sub_C_eq
    (q : ℕ) [Fact q.Prime] (W : Type) [CommRing W] [Nontrivial W]
    (T : Finset W) (hT : ∏ t ∈ T, (Polynomial.X - Polynomial.C t) = (Polynomial.X ^ q - Polynomial.X : Polynomial W)) :
    T.card = q ∧
    (∏ i : Option ↥T,
        (MvPowerSeries.C (Option.elim i (1 : W) (fun t => -(t : W))) * MvPowerSeries.X 0 +
          MvPowerSeries.C (Option.elim i (0 : W) (fun _ => (1 : W))) * MvPowerSeries.X 1 : MvPowerSeries (Fin 2) W)) =
      DrinfeldCurve.LocalChart.drinfeldForm q W ∧
    ((∀ t ∈ T, ∀ t' ∈ T, t ≠ t' → IsUnit (t - t')) →
      ∀ i j : Option ↥T, i ≠ j →
        IsUnit (Option.elim i (1 : W) (fun t => -(t : W)) * Option.elim j (0 : W) (fun _ => (1 : W)) -
          Option.elim j (1 : W) (fun t => -(t : W)) * Option.elim i (0 : W) (fun _ => (1 : W)))) := by p2m_exact_reverting @_root_.P2MW.S_DrinfeldCurve_LocalChart_card_eq_and_prod_linear_eq_drinfeldForm_and_isUnit_det_of_prod_X_sub_C_eq.solution
