import Mathlib
import Definitions.Def_AlgebraicGeometry_PicDualNumberDeformationClassSpec
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_RelPicard_exists_crossSections_of_isFrameOn_of_map_eq_oneAddEpsMul_smul
attribute [-instance] AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField
attribute [-simp] AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe AlgebraicGeometry.RelPicard.BaseChange.restrict_P AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra
  AlgebraicGeometry.Scheme.TwoAffineOpenCover
namespace AlgebraicGeometry.RelPicard

theorem exists_crossSections_of_isFrameOn_of_map_eq_oneAddEpsMul_smul
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (.of R))
    (A : Type u) [CommRing A] [Algebra R A]
    [IsSeparated (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))]
    (𝒲 𝒲' : C.TwoAffineOpenCover)
    (N : (Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R (DualNumber A))).Modules)
    (e₀ : Γ(N, (𝒲.pullback c (DualNumber A)).U0)) (e₁ : Γ(N, (𝒲.pullback c (DualNumber A)).U1))
    (g : ((𝒲.pullback c A).cover (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))).A01)
    (h₀ : Scheme.Modules.IsFrameOn e₀ (𝒲.pullback c (DualNumber A)).U0)
    (h₁ : Scheme.Modules.IsFrameOn e₁ (𝒲.pullback c (DualNumber A)).U1)
    (hg : N.presheaf.map (homOfLE inf_le_right).op e₁ =
      (show Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R (DualNumber A)),
          (𝒲.pullback c (DualNumber A)).U0 ⊓ (𝒲.pullback c (DualNumber A)).U1) from oneAddEpsMul A 𝒲 c g) •
        N.presheaf.map (homOfLE inf_le_left).op e₀)
    (e₀' : Γ(N, (𝒲'.pullback c (DualNumber A)).U0)) (e₁' : Γ(N, (𝒲'.pullback c (DualNumber A)).U1))
    (g' : ((𝒲'.pullback c A).cover (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))).A01)
    (h₀' : Scheme.Modules.IsFrameOn e₀' (𝒲'.pullback c (DualNumber A)).U0)
    (h₁' : Scheme.Modules.IsFrameOn e₁' (𝒲'.pullback c (DualNumber A)).U1)
    (hg' : N.presheaf.map (homOfLE inf_le_right).op e₁' =
      (show Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R (DualNumber A)),
          (𝒲'.pullback c (DualNumber A)).U0 ⊓ (𝒲'.pullback c (DualNumber A)).U1) from oneAddEpsMul A 𝒲' c g') •
        N.presheaf.map (homOfLE inf_le_left).op e₀') :
    let X' := Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A)
    let W0 := (𝒲.pullback c A).U0;  let W1 := (𝒲.pullback c A).U1
    let V0 := (𝒲'.pullback c A).U0; let V1 := (𝒲'.pullback c A).U1
    ∃ (g00 : Γ(X', W0 ⊓ V0)) (g01 : Γ(X', W0 ⊓ V1)) (g10 : Γ(X', W1 ⊓ V0)) (g11 : Γ(X', W1 ⊓ V1)),
      (X'.presheaf.map (homOfLE (inf_le_inf_right V0 inf_le_left  : (W0 ⊓ W1) ⊓ V0 ≤ W0 ⊓ V0)).op).hom g00
        = (X'.presheaf.map (homOfLE (inf_le_inf_right V0 inf_le_right : (W0 ⊓ W1) ⊓ V0 ≤ W1 ⊓ V0)).op).hom g10
          + (X'.presheaf.map (homOfLE (inf_le_left : (W0 ⊓ W1) ⊓ V0 ≤ W0 ⊓ W1)).op).hom g ∧
      (X'.presheaf.map (homOfLE (inf_le_inf_right V1 inf_le_left  : (W0 ⊓ W1) ⊓ V1 ≤ W0 ⊓ V1)).op).hom g01
        = (X'.presheaf.map (homOfLE (inf_le_inf_right V1 inf_le_right : (W0 ⊓ W1) ⊓ V1 ≤ W1 ⊓ V1)).op).hom g11
          + (X'.presheaf.map (homOfLE (inf_le_left : (W0 ⊓ W1) ⊓ V1 ≤ W0 ⊓ W1)).op).hom g ∧
      (X'.presheaf.map (homOfLE (inf_le_inf_left W0 inf_le_right : W0 ⊓ (V0 ⊓ V1) ≤ W0 ⊓ V1)).op).hom g01
        = (X'.presheaf.map (homOfLE (inf_le_inf_left W0 inf_le_left  : W0 ⊓ (V0 ⊓ V1) ≤ W0 ⊓ V0)).op).hom g00
          + (X'.presheaf.map (homOfLE (inf_le_right : W0 ⊓ (V0 ⊓ V1) ≤ V0 ⊓ V1)).op).hom g' ∧
      (X'.presheaf.map (homOfLE (inf_le_inf_left W1 inf_le_right : W1 ⊓ (V0 ⊓ V1) ≤ W1 ⊓ V1)).op).hom g11
        = (X'.presheaf.map (homOfLE (inf_le_inf_left W1 inf_le_left  : W1 ⊓ (V0 ⊓ V1) ≤ W1 ⊓ V0)).op).hom g10
          + (X'.presheaf.map (homOfLE (inf_le_right : W1 ⊓ (V0 ⊓ V1) ≤ V0 ⊓ V1)).op).hom g' := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_RelPicard_exists_crossSections_of_isFrameOn_of_map_eq_oneAddEpsMul_smul.solution
end AlgebraicGeometry.RelPicard
