import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_TwoGluedProjectiveLines_exists_twoAffineOpenCover_presentation_comp_iso

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve

theorem AlgebraicGeometry.TwoGluedProjectiveLines.exists_twoAffineOpenCover_presentation_comp_iso
    {k : Type u} [Field k] [DecidableEq (RatFunc k)] {X X' : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k)) (x' : X' ⟶ Spec (CommRingCat.of k))
    (φ : X ≅ X') (hφ : φ.hom ≫ x' = x)
    (M₁ M₂ : CurveModel k (RatFunc k)) (i₁ : M₁.C ⟶ X) (i₂ : M₂.C ⟶ X)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    (hi₁ : i₁ ≫ x = M₁.toBase) (hi₂ : i₂ ≫ x = M₂.toBase)
    (hcover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ)
    {n : ℕ} (a b : Fin n → kˣ)
    (hnode : ∀ i, i₁.base (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k (a i : k))).1 =
      i₂.base (M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint k (b i : k))).1)
    (hinter : ∀ (p : M₁.C) (q : M₂.C), i₁.base p = i₂.base q →
      ∃ i, p = (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k (a i : k))).1 ∧
        q = (M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint k (b i : k))).1)
    (htrans : IsReduced (pullback i₁ i₂))
    (𝒲₀ : X.TwoAffineOpenCover)
    (hU0₁ : ((i₁ ⁻¹ᵁ 𝒲₀.U0 : M₁.C.Opens) : Set M₁.C) = {(M₁.placeEquiv.symm (RationalFunctionField.placeInfty k)).1}ᶜ)
    (hU0₂ : ((i₂ ⁻¹ᵁ 𝒲₀.U0 : M₂.C.Opens) : Set M₂.C) = {(M₂.placeEquiv.symm (RationalFunctionField.placeInfty k)).1}ᶜ)
    (hU1₁ : ((i₁ ⁻¹ᵁ 𝒲₀.U1 : M₁.C.Opens) : Set M₁.C) = {(M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k 0)).1}ᶜ)
    (hU1₂ : ((i₂ ⁻¹ᵁ 𝒲₀.U1 : M₂.C.Opens) : Set M₂.C) = {(M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint k 0)).1}ᶜ)
    (W₁ : X.Opens) [IsOpenImmersion ((i₁ ⁻¹ᵁ W₁).ι ≫ i₁)] :
    ∃ 𝒲₀' : X'.TwoAffineOpenCover,
      𝒲₀'.U0 = φ.inv ⁻¹ᵁ 𝒲₀.U0 ∧ 𝒲₀'.U1 = φ.inv ⁻¹ᵁ 𝒲₀.U1 ∧
      (i₁ ≫ φ.hom) ≫ x' = M₁.toBase ∧ (i₂ ≫ φ.hom) ≫ x' = M₂.toBase ∧
      Set.range (i₁ ≫ φ.hom).base ∪ Set.range (i₂ ≫ φ.hom).base = Set.univ ∧
      (∀ i, (i₁ ≫ φ.hom).base (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k (a i : k))).1 =
        (i₂ ≫ φ.hom).base (M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint k (b i : k))).1) ∧
      (∀ (p : M₁.C) (q : M₂.C), (i₁ ≫ φ.hom).base p = (i₂ ≫ φ.hom).base q →
        ∃ i, p = (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k (a i : k))).1 ∧
          q = (M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint k (b i : k))).1) ∧
      IsReduced (pullback (i₁ ≫ φ.hom) (i₂ ≫ φ.hom)) ∧
      (((i₁ ≫ φ.hom) ⁻¹ᵁ 𝒲₀'.U0 : M₁.C.Opens) : Set M₁.C) = {(M₁.placeEquiv.symm (RationalFunctionField.placeInfty k)).1}ᶜ ∧
      (((i₂ ≫ φ.hom) ⁻¹ᵁ 𝒲₀'.U0 : M₂.C.Opens) : Set M₂.C) = {(M₂.placeEquiv.symm (RationalFunctionField.placeInfty k)).1}ᶜ ∧
      (((i₁ ≫ φ.hom) ⁻¹ᵁ 𝒲₀'.U1 : M₁.C.Opens) : Set M₁.C) = {(M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k 0)).1}ᶜ ∧
      (((i₂ ≫ φ.hom) ⁻¹ᵁ 𝒲₀'.U1 : M₂.C.Opens) : Set M₂.C) = {(M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint k 0)).1}ᶜ ∧
      IsOpenImmersion (((i₁ ≫ φ.hom) ⁻¹ᵁ (φ.inv ⁻¹ᵁ W₁)).ι ≫ (i₁ ≫ φ.hom)) ∧
      ((φ.inv ⁻¹ᵁ W₁ : X'.Opens) : Set X') = φ.hom.base '' (W₁ : Set X) ∧
      Set.range (i₁ ≫ φ.hom).base = φ.hom.base '' Set.range i₁.base ∧
      Set.range (i₂ ≫ φ.hom).base = φ.hom.base '' Set.range i₂.base := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_TwoGluedProjectiveLines_exists_twoAffineOpenCover_presentation_comp_iso.solution
