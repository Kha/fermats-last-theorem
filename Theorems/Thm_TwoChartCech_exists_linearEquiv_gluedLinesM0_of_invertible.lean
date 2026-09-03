import Mathlib
import Definitions.Def_TwoChartCech_GluedLines
import P2M.Util
import P2M.Sol.S_TwoChartCech_exists_linearEquiv_gluedLinesM0_of_invertible

set_option autoImplicit false

open TwoChartCech LaurentPolynomial

universe u

theorem TwoChartCech.exists_linearEquiv_gluedLinesM0_of_invertible
    (k : Type u) [Field k] {s : ℕ} (a b : Fin s → kˣ) (ha : Function.Injective a) (hb : Function.Injective b)
    (P : Type u) [AddCommGroup P] [Module (gluedLinesCover k a b).A0 P]
    [Module.Invertible (gluedLinesCover k a b).A0 P] :
    ∃ μ : Fin s → kˣ, Nonempty (P ≃ₗ[(gluedLinesCover k a b).A0] ↥(gluedLinesM0 k a b μ)) := by p2m_exact_reverting @_root_.P2MW.S_TwoChartCech_exists_linearEquiv_gluedLinesM0_of_invertible.solution
