import Mathlib
import Definitions.Def_WeierstrassCurve_ConductorLevel
import Definitions.Def_WeierstrassCurve_ModularityLiftingConductor
import P2M.Util
namespace P2MW.S_WeierstrassCurve_isModularModelOfExactConductorLevel_of_level_conductorLevel

set_option autoImplicit false

theorem solution
    (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) (h : W.IsModularModelOfLevel W.conductorLevel) :
    W.IsModularModelOfExactConductorLevel :=
  ⟨W.conductorLevel, W.conductorLevel_pos, W.squarefree_conductorLevel,
    fun _ hq => W.prime_dvd_conductorLevel_iff hΔ hq, h⟩
