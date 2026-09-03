import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_SemilinearAut_eq_of_forall_smul_place_eq
attribute [-instance] AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
attribute [-simp] AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.SemilinearAut.eq_of_forall_smul_place_eq
    (F₀ : Type) [Field F₀] [Algebra (AlgebraicClosure ℚ) F₀] [IsCurveOver (AlgebraicClosure ℚ) F₀]
    [Algebra.EssFiniteType (AlgebraicClosure ℚ) F₀]
    (W W' : SemilinearAut (AlgebraicClosure ℚ) F₀)
    (hW : ∀ a : AlgebraicClosure ℚ, SemilinearAut.baseAut W a = a)
    (hW' : ∀ a : AlgebraicClosure ℚ, SemilinearAut.baseAut W' a = a)
    (h : ∀ P : Place (AlgebraicClosure ℚ) F₀, W • P = W' • P) :
    W = W' := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_SemilinearAut_eq_of_forall_smul_place_eq.solution
