import Mathlib
import Definitions.Def_ModularCurve_ComplexPlaceDictionary
import P2M.Util
import P2M.Sol.S_ModularCurve_tendsto_realize_atImInfty_coeff_zero
attribute [-simp] ModularCurve.jqNModC_one ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

set_option autoImplicit false

open UpperHalfPlane
open scoped Topology

theorem ModularCurve.tendsto_realize_atImInfty_coeff_zero (N : ℕ) [NeZero N]
    (x : ModularCurve.laurentBaseChange ℂ (ModularCurve.modularFunctionFieldFull N))
    (hx : 0 ≤ (x : LaurentSeries ℂ).order) :
    Filter.Tendsto (fun τ : ℍ => ModularCurve.realize N (x : LaurentSeries ℂ) τ) atImInfty
      (𝓝 ((x : LaurentSeries ℂ).coeff 0)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_tendsto_realize_atImInfty_coeff_zero.solution
