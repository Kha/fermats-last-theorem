import Mathlib
import Definitions.Def_ModularCurve_WeierstrassLevelCarrier
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_ModularCurve_WeierstrassGamma0Sqf
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Theorems.Thm_WeierstrassCurve_IsCyclicGenKernel_variableChange
import Theorems.Thm_WeierstrassCurve_IsTwoKernel_variableChange
import P2M.Util
namespace P2MW.S_ModularCurve_IsGamma0PowAt_variableChange

set_option autoImplicit false

universe u

open ModularCurve

theorem solution
    {T : Type u} [CommRing T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T) (p k : ℕ)
    (h : Polynomial T) (hh : ModularCurve.IsGamma0PowAt W p k h) :
    ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h)  := by
  by_cases hpk : p ^ k = 2
  · rw [ModularCurve.isGamma0PowAt_of_pow_eq_two _ hpk] at hh
    rw [ModularCurve.isGamma0PowAt_of_pow_eq_two _ hpk, ModularCurve.gamma0PowDeg, if_pos hpk]
    exact WeierstrassCurve.IsTwoKernel.variableChange W C h hh
  · rw [ModularCurve.isGamma0PowAt_of_pow_ne_two _ hpk] at hh
    rw [ModularCurve.isGamma0PowAt_of_pow_ne_two _ hpk, ModularCurve.gamma0PowDeg, if_neg hpk]
    exact WeierstrassCurve.IsCyclicGenKernel.variableChange W C p k h hh
