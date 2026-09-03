import Mathlib
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_of_isPullback_of_field
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_baseChange_of_isPullback
import P2M.Util
namespace P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_relativeGroupLaw_pullbackSnd_specMap_and_closedImmersionBySections
attribute [-simp] AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

namespace H2FieldBC

theorem main
    {S : Type} [CommRing S] {A : Scheme} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (hA : AbelianSchemePropertyBundle S f)
    (𝓛 : A.Modules) (hinv : Scheme.Modules.IsInvertible 𝓛) (hva : Scheme.Modules.ClosedImmersionBySections 𝓛 f)
    (K : Type) [Field K] [Algebra S K] :
    ∃ L' : RelativeGroupLaw K (Limits.pullback.snd f (Scheme.TwoAffineOpenCover.specMap S K)),
      AbelianSchemePropertyBundle K (Limits.pullback.snd f (Scheme.TwoAffineOpenCover.specMap S K)) ∧
      Scheme.Modules.IsInvertible
        ((Scheme.Modules.pullback (Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap S K))).obj 𝓛) ∧
      Scheme.Modules.ClosedImmersionBySections
        ((Scheme.Modules.pullback (Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap S K))).obj 𝓛)
        (Limits.pullback.snd f (Scheme.TwoAffineOpenCover.specMap S K)) := by
  have sq : IsPullback (Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap S K))
      (Limits.pullback.snd f (Scheme.TwoAffineOpenCover.specMap S K)) f (Spec.map (CommRingCat.ofHom (algebraMap S K))) :=
    IsPullback.of_hasPullback f (Scheme.TwoAffineOpenCover.specMap S K)
  refine ⟨L.baseChange (Scheme.TwoAffineOpenCover.specMap S K), ?_, Scheme.Modules.IsInvertible.pullback _ hinv, ?_⟩
  · exact GoodReductionJacobian.AbelianSchemePropertyBundle.of_isPullback_of_field hA K (algebraMap S K) _ _ sq
      (L.baseChange (Scheme.TwoAffineOpenCover.specMap S K))
  · obtain ⟨N, 𝔓, hci⟩ := hva
    obtain ⟨𝔓', -, -, sq'⟩ :=
      AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_baseChange_of_isPullback (R := S) (A := K) sq 𝔓
    exact ⟨N, 𝔓', MorphismProperty.of_isPullback (P := @IsClosedImmersion) sq' hci⟩

end H2FieldBC

theorem solution
    {S : Type} [CommRing S] {A : Scheme} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (hA : AbelianSchemePropertyBundle S f)
    (𝓛 : A.Modules) (hinv : Scheme.Modules.IsInvertible 𝓛) (hva : Scheme.Modules.ClosedImmersionBySections 𝓛 f)
    (K : Type) [Field K] [Algebra S K] :
    ∃ L' : RelativeGroupLaw K (Limits.pullback.snd f (Scheme.TwoAffineOpenCover.specMap S K)),
      AbelianSchemePropertyBundle K (Limits.pullback.snd f (Scheme.TwoAffineOpenCover.specMap S K)) ∧
      Scheme.Modules.IsInvertible
        ((Scheme.Modules.pullback (Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap S K))).obj 𝓛) ∧
      Scheme.Modules.ClosedImmersionBySections
        ((Scheme.Modules.pullback (Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap S K))).obj 𝓛)
        (Limits.pullback.snd f (Scheme.TwoAffineOpenCover.specMap S K)) :=
  H2FieldBC.main L hA 𝓛 hinv hva K
