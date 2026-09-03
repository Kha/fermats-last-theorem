import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSupportedIn
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSum
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicCurve_RelCartier
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_SheafOfModules_Monoidal

import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_RelEffCartierDiv_exists_polarisation_pair_of_block
attribute [-instance] AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback
attribute [-simp] AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong AlgebraicGeometry.RelEffCartierDiv.extendAlong_I AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra MonoidalCategory
  AlgebraicGeometry.SmoothProperCurve TensorProduct

theorem AlgebraicGeometry.RelEffCartierDiv.exists_polarisation_pair_of_block
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsSeparated c]
    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (hεU : Set.range ε.1.base ⊆ (U : Set C))
    (A : Type u) [CommRing A] [Algebra R A] [Module.Finite R A] [Module.FaithfullyFlat R A]
    (B₀ : Type u) [CommRing B₀] [Algebra R B₀] [Module.Finite R B₀] [Algebra.Etale R B₀]
    (d : ℕ) (φ₀ : TensorProduct R A B₀ ≃ₐ[A] (Fin d → A))
    (z₀ : Spec (CommRingCat.of B₀) ⟶ C) [IsClosedImmersion z₀]
    (hz₀ : z₀ ≫ c = Spec.map (CommRingCat.ofHom (algebraMap R B₀)))
    (hz₀U : Set.range z₀.base ⊆ (U : Set C))
    (r r' ρ : ℕ) (hρ : ρ = r + r' * d) :
    ∃ (zA : Spec (CommRingCat.of (TensorProduct R A B₀)) ⟶ pullback (baseChange R c A) (𝟙 (Spec (CommRingCat.of A))))
      (_ : IsClosedImmersion zA)
      (_ : zA ≫ pullback.fst (baseChange R c A) (𝟙 (Spec (CommRingCat.of A))) ≫ pullback.fst c (specMap R A) =
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := B₀)).toRingHom) ≫ z₀)
      (_ : zA ≫ pullback.snd (baseChange R c A) (𝟙 (Spec (CommRingCat.of A))) =
        Spec.map (CommRingCat.ofHom (algebraMap A (TensorProduct R A B₀))))
      (E : RelEffCartierDiv c ρ (𝟙 (Spec (CommRingCat.of R))))
      (E' : RelEffCartierDiv (baseChange R c A) ρ (𝟙 (Spec (CommRingCat.of A)))),
      E.SupportedIn U ∧ E'.SupportedIn (pullback.fst c (specMap R A) ⁻¹ᵁ U) ∧
      E.I = (sectionIdeal c ε (𝟙 (Spec (CommRingCat.of R)))) ^ r *
        ((pullback.lift z₀ (Spec.map (CommRingCat.ofHom (algebraMap R B₀))) (by rw [Category.comp_id]; exact hz₀)).ker) ^ r' ∧
      E'.I = (sectionIdeal (baseChange R c A) (sectionBaseChange A ε) (𝟙 (Spec (CommRingCat.of A)))) ^ r * zA.ker ^ r' ∧
      (∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ Spec (CommRingCat.of A)), ((E'.pullbackAlong t (Category.comp_id t)).I).IsInvertible) ∧
      (∀ ⦃T T' : Scheme.{u}⦄ {t : T ⟶ Spec (CommRingCat.of A)} {t' : T' ⟶ Spec (CommRingCat.of A)} (ψ : SchemeHomOver t' t),
        Nonempty ((Scheme.Modules.pullback (baseChangeSnd (baseChange R c A) ψ)).obj
          (E'.pullbackAlong t (Category.comp_id t)).lineBundle ≅ (E'.pullbackAlong t' (Category.comp_id t')).lineBundle)) ∧
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (sΩ : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of A))
        (φ : pullback (baseChange R c A) sΩ ≅ pullback c (sΩ ≫ specMap R A)),
        φ.hom ≫ pullback.fst c (sΩ ≫ specMap R A) =
          pullback.fst (baseChange R c A) sΩ ≫ pullback.fst c (specMap R A) →
        Nonempty ((Scheme.Modules.pullback φ.hom).obj
            (E.pullbackAlong (sΩ ≫ specMap R A) (Category.comp_id _)).lineBundle ≅
          (E'.pullbackAlong sΩ (Category.comp_id sΩ)).lineBundle)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_RelEffCartierDiv_exists_polarisation_pair_of_block.solution
