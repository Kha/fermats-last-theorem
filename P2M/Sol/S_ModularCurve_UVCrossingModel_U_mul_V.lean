import Definitions.Def_ModularCurve_UVCrossingModel
import P2M.Util
namespace P2MW.S_ModularCurve_UVCrossingModel_U_mul_V

open ModularCurve ModularCurve.UVCrossingModel

theorem solution {W : Type*} [CommRing W] (π : W) :
    U π * V π = const π π :=
  by
  show Ideal.Quotient.mk _ _ * Ideal.Quotient.mk _ _ = Ideal.Quotient.mk _ _
  rw [← map_mul, Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  exact Ideal.subset_span rfl
