import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_SmoothProperCurve_isProper_and_smooth_and_geometricallyIntegral_and_nonempty_section_pullback_of_henselianLocalRing
attribute [-instance] AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField
attribute [-simp] AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

theorem AlgebraicGeometry.SmoothProperCurve.isProper_and_smooth_and_geometricallyIntegral_and_nonempty_section_pullback_of_henselianLocalRing
    {R₀ : Type} [CommRing R₀] {X : Scheme.{0}} (πX : X ⟶ Spec (CommRingCat.of R₀))
    [IsProper πX] [SmoothOfRelativeDimension 1 πX]
    (hgeo : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R₀)),
      AlgebraicGeometry.IsIntegral (pullback πX s))
    (O : Type) [CommRing O] [HenselianLocalRing O] [IsAlgClosed (IsLocalRing.ResidueField O)] (j : R₀ →+* O) :
    IsProper (pullback.snd πX (Spec.map (CommRingCat.ofHom j))) ∧
    SmoothOfRelativeDimension 1 (pullback.snd πX (Spec.map (CommRingCat.ofHom j))) ∧
    GeometricallyIntegral (pullback.snd πX (Spec.map (CommRingCat.ofHom j))) ∧
    Nonempty (SchemeHomOver (𝟙 (Spec (CommRingCat.of O))) (pullback.snd πX (Spec.map (CommRingCat.ofHom j)))) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_SmoothProperCurve_isProper_and_smooth_and_geometricallyIntegral_and_nonempty_section_pullback_of_henselianLocalRing.solution
