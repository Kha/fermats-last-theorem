import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import P2M.Util
import P2M.Sol.S_ModularCurve_UVCrossingModel_ringKrullDim_le_two

set_option autoImplicit false

universe u
open ModularCurve ModularCurve.UVCrossingModel IsLocalRing in

theorem ModularCurve.UVCrossingModel.ringKrullDim_le_two
    {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (π : W) (hπ : Irreducible π) (E : ℕ) (hE : 1 ≤ E) :
    ringKrullDim (UVCrossingModel W (π ^ E)) ≤ 2 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_UVCrossingModel_ringKrullDim_le_two.solution
