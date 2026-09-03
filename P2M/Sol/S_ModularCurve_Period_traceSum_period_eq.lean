import Definitions.Def_ModularCurve_PeriodMap
import Definitions.Def_ModularCurve_PeriodTransfer
import P2M.Util
namespace P2MW.S_ModularCurve_Period_traceSum_period_eq

set_option autoImplicit false

open scoped MatrixGroups

open ModularCurve.Period

theorem solution :
    ∀ {Γ Δ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)}
      {F : UpperHalfPlane → ℂ} [inst : Fintype (↥Γ ⧸ Δ.subgroupOf Γ)]
      (hF : ModularCurve.Period.IsEquivariantPrimitive Δ F) (γ : ↥Γ),
      (ModularCurve.Period.IsEquivariantPrimitive.traceSum hF).period γ =
        ∑ q, hF.period (ModularCurve.Period.transferElt γ q) := by
  intro Γ Δ F inst hF γ
  rw [← IsEquivariantPrimitive.sub_eq_period hF.traceSum γ UpperHalfPlane.I]
  exact sum_traceRep_smul_sub hF γ UpperHalfPlane.I

#print axioms solution
