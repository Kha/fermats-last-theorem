import Mathlib
import Definitions.Def_ModularCurve_X1HeckeModule
import P2M.Util
import P2M.Sol.S_ModularCurve_JOne_galois_smul_heckeAlgOne_smul

set_option autoImplicit false

theorem ModularCurve.JOne.galois_smul_heckeAlgOne_smul (M : ℕ) [NeZero M]
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (t : ModularCurve.HeckeAlgOne)
    (x : ModularCurve.JOne M) :
    letI := ModularCurve.heckeModuleOneBar M
    σ • (t • x) = t • (σ • x) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_JOne_galois_smul_heckeAlgOne_smul.solution
