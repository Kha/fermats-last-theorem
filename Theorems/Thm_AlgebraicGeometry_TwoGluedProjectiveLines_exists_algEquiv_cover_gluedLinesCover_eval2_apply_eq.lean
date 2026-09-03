import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Definitions.Def_TwoChartCech_GluedLines
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_TwoGluedProjectiveLines_exists_algEquiv_cover_gluedLinesCover_eval2_apply_eq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve

universe u

theorem AlgebraicGeometry.TwoGluedProjectiveLines.exists_algEquiv_cover_gluedLinesCover_eval2_apply_eq
    (k : Type u) [Field k] [DecidableEq (RatFunc k)]
    {X : Scheme.{u}} (x : X ⟶ Spec (.of k)) [IsReduced X]
    (M₁ M₂ : CurveModel k (RatFunc k)) (i₁ : M₁.C ⟶ X) (i₂ : M₂.C ⟶ X)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    (hi₁ : i₁ ≫ x = M₁.toBase) (hi₂ : i₂ ≫ x = M₂.toBase)
    (hcover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ)
    {s : ℕ} (a b : Fin s → kˣ) (ha : Function.Injective a)
    (hnode : ∀ i, i₁.base (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k (a i : k))).1 =
      i₂.base (M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint k (b i : k))).1)
    (hinter : ∀ (p : M₁.C) (q : M₂.C), i₁.base p = i₂.base q →
      ∃ i, p = (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k (a i : k))).1 ∧
        q = (M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint k (b i : k))).1)
    (htrans : IsReduced (pullback i₁ i₂))
    (𝒲₀ : X.TwoAffineOpenCover)
    (hU0₁ : ((i₁ ⁻¹ᵁ 𝒲₀.U0 : M₁.C.Opens) : Set M₁.C) =
      {(M₁.placeEquiv.symm (RationalFunctionField.placeInfty k)).1}ᶜ)
    (hU0₂ : ((i₂ ⁻¹ᵁ 𝒲₀.U0 : M₂.C.Opens) : Set M₂.C) =
      {(M₂.placeEquiv.symm (RationalFunctionField.placeInfty k)).1}ᶜ)
    (hU1₁ : ((i₁ ⁻¹ᵁ 𝒲₀.U1 : M₁.C.Opens) : Set M₁.C) =
      {(M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k 0)).1}ᶜ)
    (hU1₂ : ((i₂ ⁻¹ᵁ 𝒲₀.U1 : M₂.C.Opens) : Set M₂.C) =
      {(M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint k 0)).1}ᶜ)
 :
    ∃ (φ₀ : (𝒲₀.cover x).A0 ≃ₐ[k] (TwoChartCech.gluedLinesCover k a b).A0)
      (φ₁ : (𝒲₀.cover x).A1 ≃ₐ[k] (TwoChartCech.gluedLinesCover k a b).A1)
      (φ₀₁ : (𝒲₀.cover x).A01 ≃ₐ[k] (TwoChartCech.gluedLinesCover k a b).A01),
      (∀ f, φ₀₁ ((𝒲₀.cover x).ρ0 f) = (TwoChartCech.gluedLinesCover k a b).ρ0 (φ₀ f)) ∧
      (∀ f, φ₀₁ ((𝒲₀.cover x).ρ1 f) = (TwoChartCech.gluedLinesCover k a b).ρ1 (φ₁ f)) ∧
      (∀ [Nonempty (i₁ ⁻¹ᵁ 𝒲₀.U0 : M₁.C.Opens)] [Nonempty (i₂ ⁻¹ᵁ 𝒲₀.U0 : M₂.C.Opens)] (f : (𝒲₀.cover x).A0),
        LaurentPolynomial.eval₂ (algebraMap k (RatFunc k)) (Units.mk0 (RatFunc.X : RatFunc k) RatFunc.X_ne_zero)
            ((φ₀ f : (TwoChartCech.gluedLinesCover k a b).A0) : LaurentPolynomial k × LaurentPolynomial k).1 =
          ((M₁.ffEquiv.symm : M₁.C.functionField ≃+* RatFunc k).toRingHom.comp
            (algebraMap Γ(M₁.C, i₁ ⁻¹ᵁ 𝒲₀.U0) M₁.C.functionField)) ((i₁.app 𝒲₀.U0) f) ∧
        LaurentPolynomial.eval₂ (algebraMap k (RatFunc k)) (Units.mk0 (RatFunc.X : RatFunc k) RatFunc.X_ne_zero)
            ((φ₀ f : (TwoChartCech.gluedLinesCover k a b).A0) : LaurentPolynomial k × LaurentPolynomial k).2 =
          ((M₂.ffEquiv.symm : M₂.C.functionField ≃+* RatFunc k).toRingHom.comp
            (algebraMap Γ(M₂.C, i₂ ⁻¹ᵁ 𝒲₀.U0) M₂.C.functionField)) ((i₂.app 𝒲₀.U0) f)) ∧
      (∀ [Nonempty (i₁ ⁻¹ᵁ 𝒲₀.U1 : M₁.C.Opens)] [Nonempty (i₂ ⁻¹ᵁ 𝒲₀.U1 : M₂.C.Opens)] (f : (𝒲₀.cover x).A1),
        LaurentPolynomial.eval₂ (algebraMap k (RatFunc k)) (Units.mk0 (RatFunc.X : RatFunc k) RatFunc.X_ne_zero)
            ((φ₁ f : (TwoChartCech.gluedLinesCover k a b).A1) : LaurentPolynomial k × LaurentPolynomial k).1 =
          ((M₁.ffEquiv.symm : M₁.C.functionField ≃+* RatFunc k).toRingHom.comp
            (algebraMap Γ(M₁.C, i₁ ⁻¹ᵁ 𝒲₀.U1) M₁.C.functionField)) ((i₁.app 𝒲₀.U1) f) ∧
        LaurentPolynomial.eval₂ (algebraMap k (RatFunc k)) (Units.mk0 (RatFunc.X : RatFunc k) RatFunc.X_ne_zero)
            ((φ₁ f : (TwoChartCech.gluedLinesCover k a b).A1) : LaurentPolynomial k × LaurentPolynomial k).2 =
          ((M₂.ffEquiv.symm : M₂.C.functionField ≃+* RatFunc k).toRingHom.comp
            (algebraMap Γ(M₂.C, i₂ ⁻¹ᵁ 𝒲₀.U1) M₂.C.functionField)) ((i₂.app 𝒲₀.U1) f)) ∧
      (∀ [Nonempty (i₁ ⁻¹ᵁ (𝒲₀.U0 ⊓ 𝒲₀.U1) : M₁.C.Opens)] [Nonempty (i₂ ⁻¹ᵁ (𝒲₀.U0 ⊓ 𝒲₀.U1) : M₂.C.Opens)] (f : (𝒲₀.cover x).A01),
        LaurentPolynomial.eval₂ (algebraMap k (RatFunc k)) (Units.mk0 (RatFunc.X : RatFunc k) RatFunc.X_ne_zero)
            ((φ₀₁ f : (TwoChartCech.gluedLinesCover k a b).A01) : LaurentPolynomial k × LaurentPolynomial k).1 =
          ((M₁.ffEquiv.symm : M₁.C.functionField ≃+* RatFunc k).toRingHom.comp
            (algebraMap Γ(M₁.C, i₁ ⁻¹ᵁ (𝒲₀.U0 ⊓ 𝒲₀.U1)) M₁.C.functionField)) ((i₁.app (𝒲₀.U0 ⊓ 𝒲₀.U1)) f) ∧
        LaurentPolynomial.eval₂ (algebraMap k (RatFunc k)) (Units.mk0 (RatFunc.X : RatFunc k) RatFunc.X_ne_zero)
            ((φ₀₁ f : (TwoChartCech.gluedLinesCover k a b).A01) : LaurentPolynomial k × LaurentPolynomial k).2 =
          ((M₂.ffEquiv.symm : M₂.C.functionField ≃+* RatFunc k).toRingHom.comp
            (algebraMap Γ(M₂.C, i₂ ⁻¹ᵁ (𝒲₀.U0 ⊓ 𝒲₀.U1)) M₂.C.functionField)) ((i₂.app (𝒲₀.U0 ⊓ 𝒲₀.U1)) f)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_TwoGluedProjectiveLines_exists_algEquiv_cover_gluedLinesCover_eval2_apply_eq.solution
