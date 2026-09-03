import Mathlib
import Definitions.Def_ModularCurve_ComplexPlaceDictionary
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_analyticAt_realize_eq_qParam_zpow_mul
attribute [-simp] ModularCurve.jqNModC_one ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

set_option autoImplicit false

open UpperHalfPlane
open scoped Topology

theorem ModularCurve.exists_analyticAt_realize_eq_qParam_zpow_mul (N : ℕ) [NeZero N]
    (x : ModularCurve.laurentBaseChange ℂ (ModularCurve.modularFunctionFieldFull N)) (hx : x ≠ 0) :
    ∃ G : ℂ → ℂ, AnalyticAt ℂ G 0 ∧
      G 0 = (x : LaurentSeries ℂ).coeff (x : LaurentSeries ℂ).order ∧
      ∀ᶠ τ in atImInfty, ModularCurve.realize N (x : LaurentSeries ℂ) τ =
        Function.Periodic.qParam 1 (τ : ℂ) ^ (x : LaurentSeries ℂ).order *
          G (Function.Periodic.qParam 1 (τ : ℂ)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_analyticAt_realize_eq_qParam_zpow_mul.solution
