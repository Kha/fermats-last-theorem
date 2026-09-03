import Definitions.Def_ModularCurve_FullLevelJacobian
import P2M.Util
import P2M.Sol.S_ModularCurve_FullLevel_tateHecke_mul_tateGal_comm

set_option autoImplicit false

theorem ModularCurve.FullLevel.tateHecke_mul_tateGal_comm
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (lam : ℕ) [Fact lam.Prime] :
    ∀ (t : ModularCurve.HeckeAlg) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
      ModularCurve.FullLevel.tateHecke q M' lam t * ModularCurve.FullLevel.tateGal q M' lam σ =
        ModularCurve.FullLevel.tateGal q M' lam σ * ModularCurve.FullLevel.tateHecke q M' lam t := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_FullLevel_tateHecke_mul_tateGal_comm.solution
