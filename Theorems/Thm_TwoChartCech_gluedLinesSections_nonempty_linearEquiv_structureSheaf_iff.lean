import Mathlib
import Definitions.Def_TwoChartCech_GluedLines
import P2M.Util
import P2M.Sol.S_TwoChartCech_gluedLinesSections_nonempty_linearEquiv_structureSheaf_iff

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

universe u

open LaurentPolynomial TwoChartCech

theorem TwoChartCech.gluedLinesSections_nonempty_linearEquiv_structureSheaf_iff (k : Type u) [Field k] {s : ℕ}
    (a b : Fin s → kˣ) (hb : Function.Injective b) (lam : Fin s → kˣ) (n m : ℤ) :
    letI := (gluedLinesSections k a b lam n m).M0_moduleA
    letI := (gluedLinesSections k a b lam n m).M1_moduleA
    letI := (gluedLinesSections k a b lam n m).M01_moduleA
    (∃ (g₀ : (gluedLinesSections k a b lam n m).M0 ≃ₗ[(gluedLinesCover k a b).A0] (gluedLinesCover k a b).structureSheaf.M0)
       (g₁ : (gluedLinesSections k a b lam n m).M1 ≃ₗ[(gluedLinesCover k a b).A1] (gluedLinesCover k a b).structureSheaf.M1)
       (g₀₁ : (gluedLinesSections k a b lam n m).M01 ≃ₗ[(gluedLinesCover k a b).A01] (gluedLinesCover k a b).structureSheaf.M01),
       (∀ t, g₀₁ ((gluedLinesSections k a b lam n m).r0 t) = (gluedLinesCover k a b).structureSheaf.r0 (g₀ t)) ∧
       (∀ t, g₀₁ ((gluedLinesSections k a b lam n m).r1 t) = (gluedLinesCover k a b).structureSheaf.r1 (g₁ t)))
     ↔ (n = 0 ∧ m = 0 ∧ ∀ i j, lam i = lam j) := by p2m_exact_reverting @_root_.P2MW.S_TwoChartCech_gluedLinesSections_nonempty_linearEquiv_structureSheaf_iff.solution
