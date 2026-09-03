import Mathlib
import Definitions.Def_ModularCurve_HeckeDifferential
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverKaehler
import Definitions.Def_AlgebraicCurve_KaehlerToFunctionField
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_ringEquiv_functionField_pullback_comp_baseToFunctionField_eq_and_germToFunctionField_eq_chartMap_of_neZero
attribute [-instance] ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois
attribute [-simp] ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve~baseChangeEquiv AlgebraicCurve"

theorem ModularCurve.exists_ringEquiv_functionField_pullback_comp_baseToFunctionField_eq_and_germToFunctionField_eq_chartMap_of_neZero
    (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime]
    {X : Scheme.{0}} (c : X ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))) [IsIntegral X] [IsProper c]
    [SmoothOfRelativeDimension 1 c] (𝒱 : X.TwoAffineOpenCover)
    (ι : (𝒱.cover c).A0 →+* ↥(modularFunctionFieldBar N))
    (hιR : ι.comp (algebraMap ↥(GaloisRep.ratLocalizedAt p) (𝒱.cover c).A0) =
      (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)).comp (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)))
    (hιinj : Function.Injective ι)
    (hιrat : ∀ a : (𝒱.cover c).A0, ∃ x ∈ modularFunctionFieldFull N,
      coeffEmb (AlgebraicClosure ℚ) x = (ι a : LaurentSeries (AlgebraicClosure ℚ)))
    (hιfrac : ∀ x ∈ modularFunctionFieldFull N, ∃ a b : (𝒱.cover c).A0, ι b ≠ 0 ∧
      coeffEmb (AlgebraicClosure ℚ) x * (ι b : LaurentSeries (AlgebraicClosure ℚ)) = ι a)
    [IsIntegral (pullback c (Scheme.TwoAffineOpenCover.specMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)))] [Nonempty (𝒱.pullback c (AlgebraicClosure ℚ)).U0] :
    ∃ Φ : (pullback c (Scheme.TwoAffineOpenCover.specMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))).functionField ≃+* ↥(modularFunctionFieldBar N),
      Φ.toRingHom.comp (baseToFunctionField (pullback.snd c (Scheme.TwoAffineOpenCover.specMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)))) = algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) ∧
      ∀ a : (𝒱.cover c).A0,
        Φ (((pullback c (Scheme.TwoAffineOpenCover.specMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))).germToFunctionField (𝒱.pullback c (AlgebraicClosure ℚ)).U0).hom
          ((Scheme.TwoAffineOpenCover.HomOver.baseChange 𝒱 c (AlgebraicClosure ℚ)).ringHom0 a)) = ι a := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_ringEquiv_functionField_pullback_comp_baseToFunctionField_eq_and_germToFunctionField_eq_chartMap_of_neZero.solution
