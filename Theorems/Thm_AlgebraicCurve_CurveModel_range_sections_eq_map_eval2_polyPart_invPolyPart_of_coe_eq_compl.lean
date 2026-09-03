import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Definitions.Def_TwoChartCech_GluedLines
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_CurveModel_range_sections_eq_map_eval2_polyPart_invPolyPart_of_coe_eq_compl

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicCurve

universe u

theorem AlgebraicCurve.CurveModel.range_sections_eq_map_eval2_polyPart_invPolyPart_of_coe_eq_compl
    (K : Type u) [Field K] [DecidableEq (RatFunc K)]
    (M : CurveModel K (RatFunc K)) (U V : M.C.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : IsAffineOpen (U ⊓ V))
    [Nonempty U] [Nonempty V] [Nonempty (U ⊓ V : M.C.Opens)]
    (hUset : ((U : Set M.C)) = {(M.placeEquiv.symm (RationalFunctionField.placeInfty K)).1}ᶜ)
    (hVset : ((V : Set M.C)) = {(M.placeEquiv.symm (RationalFunctionField.placeOfPoint K 0)).1}ᶜ) :
    Function.Injective
        (LaurentPolynomial.eval₂ (algebraMap K (RatFunc K)) (Units.mk0 (RatFunc.X : RatFunc K) RatFunc.X_ne_zero)) ∧
      ((M.ffEquiv.symm : M.C.functionField ≃+* RatFunc K).toRingHom.comp
          (algebraMap Γ(M.C, U) M.C.functionField)).range =
        ((TwoChartCech.polyPart K).toSubring).map
          (LaurentPolynomial.eval₂ (algebraMap K (RatFunc K)) (Units.mk0 (RatFunc.X : RatFunc K) RatFunc.X_ne_zero)) ∧
      ((M.ffEquiv.symm : M.C.functionField ≃+* RatFunc K).toRingHom.comp
          (algebraMap Γ(M.C, V) M.C.functionField)).range =
        ((TwoChartCech.invPolyPart K).toSubring).map
          (LaurentPolynomial.eval₂ (algebraMap K (RatFunc K)) (Units.mk0 (RatFunc.X : RatFunc K) RatFunc.X_ne_zero)) ∧
      ((M.ffEquiv.symm : M.C.functionField ≃+* RatFunc K).toRingHom.comp
          (algebraMap Γ(M.C, U ⊓ V) M.C.functionField)).range =
        (LaurentPolynomial.eval₂ (algebraMap K (RatFunc K))
          (Units.mk0 (RatFunc.X : RatFunc K) RatFunc.X_ne_zero)).range := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_CurveModel_range_sections_eq_map_eval2_polyPart_invPolyPart_of_coe_eq_compl.solution
