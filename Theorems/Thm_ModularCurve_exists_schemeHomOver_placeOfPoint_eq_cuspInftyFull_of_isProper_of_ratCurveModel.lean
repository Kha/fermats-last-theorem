import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_ModularCurve_QAdicPlace
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_schemeHomOver_placeOfPoint_eq_cuspInftyFull_of_isProper_of_ratCurveModel

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve NeronModelInfra ModularCurve

theorem ModularCurve.exists_schemeHomOver_placeOfPoint_eq_cuspInftyFull_of_isProper_of_ratCurveModel
    (p : ℕ) [NeZero p] (q : ℕ) [Fact q.Prime]
    {X : Scheme.{0}} (c : X ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt q))) [IsProper c]
    (M₀ : CurveModel ℚ ↥(modularFunctionFieldFull p))
    (e₀ : M₀.C ⟶ pullback c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt q) ℚ))))
    [IsIso e₀]
    (he₀ : e₀ ≫ pullback.snd c _ = M₀.toBase) :
    ∃ (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt q)))) c)
      (x₀ : closedPoints M₀.C)
      (y : Spec (CommRingCat.of ℚ) ⟶
        pullback c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt q) ℚ)))),
      M₀.placeOfPoint x₀ = cuspInftyFull p ∧
      y ≫ pullback.snd c _ = 𝟙 _ ∧
      y ≫ pullback.fst c _ =
        Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt q) ℚ)) ≫ ε.1 ∧
      (y ≫ inv e₀).base (IsLocalRing.closedPoint ℚ) = x₀.1 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_schemeHomOver_placeOfPoint_eq_cuspInftyFull_of_isProper_of_ratCurveModel.solution
