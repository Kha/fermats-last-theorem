import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import P2M.Util
import P2M.Sol.S_ModularCurve_UVCrossingModel_nontrivial_of_not_isUnit

open ModularCurve ModularCurve.UVCrossingModel
theorem ModularCurve.UVCrossingModel.nontrivial_of_not_isUnit {W : Type*} [CommRing W] {π : W} (hπ : ¬IsUnit π) : Nontrivial (UVCrossingModel W π) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_UVCrossingModel_nontrivial_of_not_isUnit.solution
