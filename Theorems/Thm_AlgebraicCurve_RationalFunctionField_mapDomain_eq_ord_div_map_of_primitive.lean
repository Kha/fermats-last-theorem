import Mathlib
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_RationalFunctionField_mapDomain_eq_ord_div_map_of_primitive
attribute [-instance] AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions
attribute [-simp] AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one

set_option autoImplicit false

open Polynomial AlgebraicCurve AlgebraicCurve.RationalFunctionField
theorem AlgebraicCurve.RationalFunctionField.mapDomain_eq_ord_div_map_of_primitive
    {L : Type*} [Field L] [IsAlgClosed L] [DecidableEq (RatFunc L)] {A : ValuationSubring L}
    {k : Type*} [Field k] [DecidableEq (RatFunc k)] (red : A →+* k)
    (hred : ∀ a : A, a ∈ IsLocalRing.maximalIdeal A → red a = 0)
    (sp : Place L (RatFunc L) → Place k (RatFunc k))
    (hsp_int : ∀ a : A, sp (placeOfPoint L (a : L)) = placeOfPoint k (red a))
    (hsp_out : ∀ a : L, a ∉ A → sp (placeOfPoint L a) = placeInfty k)
    (hsp_infty : sp (placeInfty L) = placeInfty k)
    (P Q : Polynomial A) (hP : ∃ i, P.coeff i ∉ IsLocalRing.maximalIdeal A)
    (hQ : ∃ i, Q.coeff i ∉ IsLocalRing.maximalIdeal A)
    (D : Divisor L (RatFunc L))
    (hD : ∀ w, D w = w.ord (algebraMap (Polynomial L) (RatFunc L) (P.map (algebraMap A L))
                              / algebraMap (Polynomial L) (RatFunc L) (Q.map (algebraMap A L)))) :
    ∀ v' : Place k (RatFunc k),
      Finsupp.mapDomain sp D v'
        = v'.ord (algebraMap (Polynomial k) (RatFunc k) (P.map red)
                  / algebraMap (Polynomial k) (RatFunc k) (Q.map red)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_RationalFunctionField_mapDomain_eq_ord_div_map_of_primitive.solution
