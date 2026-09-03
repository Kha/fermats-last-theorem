import Definitions.Def_ModularCurve_KroneckerTransport
import P2M.Util
namespace P2MW.S_ModularCurve_ModularPolynomialData_eval_int_eq_zero

open PowerSeries HahnSeries IntermediateField ModularCurve

theorem solution {N : ℕ} [NeZero N]
    (data : ModularCurve.ModularPolynomialData N) :
    data.Φ.eval₂ ModularCurve.evalAtJInt (ModularCurve.jqIntN N) = 0 := by
  refine laurentMap_injective (f := Int.castRingHom ℚ) Int.cast_injective ?_
  rw [map_zero, Polynomial.hom_eval₂, laurentMap_comp_evalAtJInt, laurentMap_jqIntN]
  exact data.eval_eq_zero
