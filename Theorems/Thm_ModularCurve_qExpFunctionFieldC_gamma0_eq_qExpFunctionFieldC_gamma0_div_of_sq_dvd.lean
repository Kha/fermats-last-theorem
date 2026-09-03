import Mathlib
import Definitions.Def_ModularCurve_X1
import P2M.Util
import P2M.Sol.S_ModularCurve_qExpFunctionFieldC_gamma0_eq_qExpFunctionFieldC_gamma0_div_of_sq_dvd
attribute [-instance] WeierstrassCurve.Affine.Point.instFinite
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU

set_option autoImplicit false

theorem ModularCurve.qExpFunctionFieldC_gamma0_eq_qExpFunctionFieldC_gamma0_div_of_sq_dvd
    (K : Type*) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (N : ℕ) [NeZero N] (hp2N : p ^ 2 ∣ N) :
    ModularCurve.qExpFunctionFieldC K (CongruenceSubgroup.Gamma0 N) =
      ModularCurve.qExpFunctionFieldC K (CongruenceSubgroup.Gamma0 (N / p)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_qExpFunctionFieldC_gamma0_eq_qExpFunctionFieldC_gamma0_div_of_sq_dvd.solution
