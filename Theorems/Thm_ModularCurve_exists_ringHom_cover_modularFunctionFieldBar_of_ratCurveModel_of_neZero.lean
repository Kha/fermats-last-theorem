import Mathlib
import Definitions.Def_ModularCurve_HeckeDifferential
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverKaehler
import Definitions.Def_AlgebraicCurve_CurveModel
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_ringHom_cover_modularFunctionFieldBar_of_ratCurveModel_of_neZero
attribute [-instance] NeronModelInfra.isOpenImmersion_specGenericFibreInclusion NeronModelInfra.isLocalizationAway_uniformizer_zp

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve AlgebraicCurve

theorem ModularCurve.exists_ringHom_cover_modularFunctionFieldBar_of_ratCurveModel_of_neZero
    (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime]
    {X : Scheme.{0}} (c : X ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))) [IsIntegral X] (𝒱 : X.TwoAffineOpenCover)
    (M₀ : CurveModel ℚ ↥(modularFunctionFieldFull N))
    (e₀ : M₀.C ⟶ pullback c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ)))) [IsIso e₀]
    (he₀ : e₀ ≫ pullback.snd c _ = M₀.toBase)
    (hgen0 : genericPoint M₀.C ∈ (e₀ ≫ pullback.fst c _) ⁻¹ᵁ 𝒱.U0)
    (hgen01 : genericPoint M₀.C ∈ (e₀ ≫ pullback.fst c _) ⁻¹ᵁ (𝒱.U0 ⊓ 𝒱.U1)) :
    ∃ (ι : (𝒱.cover c).A0 →+* ↥(modularFunctionFieldBar N)) (ι₀₁ : (𝒱.cover c).A01 →+* ↥(modularFunctionFieldBar N)),

      (∀ a : (𝒱.cover c).A0, ((ι a : ↥(modularFunctionFieldBar N)) : LaurentSeries (AlgebraicClosure ℚ)) =
        coeffEmb (AlgebraicClosure ℚ) (((M₀.ffEquiv.symm ((M₀.C.presheaf.germ ((e₀ ≫ pullback.fst c _) ⁻¹ᵁ 𝒱.U0) (genericPoint M₀.C) hgen0).hom (((e₀ ≫ pullback.fst c _).app (𝒱.U0)).hom a))) : ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ)) ∧
      (∀ a : (𝒱.cover c).A01, ((ι₀₁ a : ↥(modularFunctionFieldBar N)) : LaurentSeries (AlgebraicClosure ℚ)) =
        coeffEmb (AlgebraicClosure ℚ) (((M₀.ffEquiv.symm ((M₀.C.presheaf.germ ((e₀ ≫ pullback.fst c _) ⁻¹ᵁ (𝒱.U0 ⊓ 𝒱.U1)) (genericPoint M₀.C) hgen01).hom (((e₀ ≫ pullback.fst c _).app (𝒱.U0 ⊓ 𝒱.U1)).hom a))) : ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ)) ∧
      (∀ a : (𝒱.cover c).A0, ι₀₁ ((𝒱.cover c).ρ0 a) = ι a) ∧

      ι.comp (algebraMap ↥(GaloisRep.ratLocalizedAt p) (𝒱.cover c).A0) =
        (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)).comp (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)) ∧
      ι₀₁.comp (algebraMap ↥(GaloisRep.ratLocalizedAt p) (𝒱.cover c).A01) =
        (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)).comp (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)) ∧

      Function.Injective ι ∧ Function.Injective ι₀₁ ∧

      (∀ a : (𝒱.cover c).A0, ∃ x ∈ modularFunctionFieldFull N,
        coeffEmb (AlgebraicClosure ℚ) x = (ι a : LaurentSeries (AlgebraicClosure ℚ))) ∧

      (∀ x ∈ modularFunctionFieldFull N, ∃ a b : (𝒱.cover c).A0, ι b ≠ 0 ∧
        coeffEmb (AlgebraicClosure ℚ) x * (ι b : LaurentSeries (AlgebraicClosure ℚ)) = ι a) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_ringHom_cover_modularFunctionFieldBar_of_ratCurveModel_of_neZero.solution
