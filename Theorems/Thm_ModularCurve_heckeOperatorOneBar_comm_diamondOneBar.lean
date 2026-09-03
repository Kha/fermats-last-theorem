import Mathlib
import Definitions.Def_ModularCurve_X1HeckeModule
import P2M.Util
import P2M.Sol.S_ModularCurve_heckeOperatorOneBar_comm_diamondOneBar
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

theorem ModularCurve.heckeOperatorOneBar_comm_diamondOneBar (M : ℕ) [NeZero M] (ℓ : Nat.Primes)
    (d : ℕ) :
    ModularCurve.heckeOperatorOneBar M ℓ * ModularCurve.diamondOneBar M d =
      ModularCurve.diamondOneBar M d * ModularCurve.heckeOperatorOneBar M ℓ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_heckeOperatorOneBar_comm_diamondOneBar.solution
