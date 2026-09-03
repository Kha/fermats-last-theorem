import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import P2M.Util
import P2M.Sol.S_ModularCurve_UVCrossingModel_U_notMem_fixedSubring

open ModularCurve ModularCurve.UVCrossingModel
theorem ModularCurve.UVCrossingModel.U_notMem_fixedSubring {W : Type*} [CommRing W] (π : W) [Nontrivial (W ⧸ Ideal.span {π})] : U π ∉ fixedSubring π := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_UVCrossingModel_U_notMem_fixedSubring.solution
