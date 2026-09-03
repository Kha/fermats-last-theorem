import Definitions.Def_ModularCurve_PeriodMap
import Definitions.Def_ModularCurve_PeriodTransfer
import P2M.Util
import P2M.Sol.S_ModularCurve_Period_traceSum_period_eq
open scoped MatrixGroups
theorem ModularCurve.Period.traceSum_period_eq :
    ∀ {Γ Δ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)}
      {F : UpperHalfPlane → ℂ} [inst : Fintype (↥Γ ⧸ Δ.subgroupOf Γ)]
      (hF : ModularCurve.Period.IsEquivariantPrimitive Δ F) (γ : ↥Γ),
      (ModularCurve.Period.IsEquivariantPrimitive.traceSum hF).period γ =
        ∑ q, hF.period (ModularCurve.Period.transferElt γ q) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_Period_traceSum_period_eq.solution
