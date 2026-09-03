import Mathlib
import Definitions.Def_WeierstrassCurve_ModularityProps
import P2M.Util
namespace P2MW.S_WeierstrassCurve_isModular_map_of_isModularModel

theorem solution {W : WeierstrassCurve ℤ} (h : W.IsModularModel) :
    (W.map (Int.castRingHom ℚ)).IsModular :=
  ⟨W, ⟨1, one_smul _ _⟩, h⟩
