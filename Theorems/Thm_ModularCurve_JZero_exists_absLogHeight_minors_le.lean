import Definitions.Def_ModularCurve_JZeroHeightForm
import Definitions.Def_ModularCurve_JZeroHeightFormPositivity
import P2M.Util
import P2M.Sol.S_ModularCurve_JZero_exists_absLogHeight_minors_le

set_option autoImplicit false

open ModularCurve AlgebraicCurve

theorem ModularCurve.JZero.exists_absLogHeight_minors_le (r : ℕ) :
    ∃ C₀ : ℝ, ∀ x y : Fin r → AlgebraicClosure ℚ,
      absLogHeight (fun p : Fin r × Fin r => x p.1 * y p.2 - x p.2 * y p.1)
        ≤ absLogHeight x + absLogHeight y + C₀ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_JZero_exists_absLogHeight_minors_le.solution
