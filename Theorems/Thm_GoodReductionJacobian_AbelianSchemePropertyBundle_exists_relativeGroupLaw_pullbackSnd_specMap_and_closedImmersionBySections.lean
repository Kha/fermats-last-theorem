import Mathlib
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_relativeGroupLaw_pullbackSnd_specMap_and_closedImmersionBySections
attribute [-simp] AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.exists_relativeGroupLaw_pullbackSnd_specMap_and_closedImmersionBySections
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
        (Limits.pullback.snd f (Scheme.TwoAffineOpenCover.specMap S K)) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_relativeGroupLaw_pullbackSnd_specMap_and_closedImmersionBySections.solution
