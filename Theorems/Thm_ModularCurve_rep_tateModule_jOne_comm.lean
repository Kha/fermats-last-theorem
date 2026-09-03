import Mathlib
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_EllipticCurve_TateModule
import P2M.Util
import P2M.Sol.S_ModularCurve_rep_tateModule_jOne_comm

theorem ModularCurve.rep_tateModule_jOne_comm (M p : ℕ) [NeZero M] [Fact p.Prime]
    (hcomm : ModularCurve.HeckeDiamondCommuteBar M)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (T : ModularCurve.HeckeAlgOne)
    (x : TateModule p (ModularCurve.JOne M)) :
    letI := ModularCurve.heckeModuleOneBar M
    TateModule.rep p (ModularCurve.JOne M) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ
        (TateModule.rep p (ModularCurve.JOne M) ModularCurve.HeckeAlgOne T x)
      = TateModule.rep p (ModularCurve.JOne M) ModularCurve.HeckeAlgOne T
        (TateModule.rep p (ModularCurve.JOne M) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ x) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_rep_tateModule_jOne_comm.solution
