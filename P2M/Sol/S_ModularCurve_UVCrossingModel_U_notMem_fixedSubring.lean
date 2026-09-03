import Definitions.Def_ModularCurve_UVCrossingModel
import Theorems.Thm_ModularCurve_UVCrossingModel_crossingSwap_U
import Theorems.Thm_ModularCurve_UVCrossingModel_U_ne_V
import P2M.Util
namespace P2MW.S_ModularCurve_UVCrossingModel_U_notMem_fixedSubring

open ModularCurve ModularCurve.UVCrossingModel in
theorem solution {W : Type*} [CommRing W] (π : W) [Nontrivial (W ⧸ Ideal.span {π})] :
    U π ∉ fixedSubring π :=
  by
  intro hmem
  rw [mem_fixedSubring_iff, ModularCurve.UVCrossingModel.crossingSwap_U] at hmem
  exact ModularCurve.UVCrossingModel.U_ne_V π hmem.symm
