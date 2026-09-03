import Definitions.Def_WeierstrassCurve_ModularityLiftingConductor
import P2M.Util
namespace P2MW.S_WeierstrassCurve_IsModularModelOfExactConductorLevel_isModularModelOfConductorLevel

theorem solution {W : WeierstrassCurve ℤ}
    (h : W.IsModularModelOfExactConductorLevel) : W.IsModularModelOfConductorLevel := by
  obtain ⟨N, hN, -, hiff, hmod⟩ := h
  exact ⟨N, hN, hmod, fun ℓ hℓ hdvd => (hiff ℓ hℓ).mpr hdvd⟩
