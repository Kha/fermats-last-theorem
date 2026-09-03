import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelSubPicPresheaf
import Definitions.Def_CategoryTheory_OverTotalPresheaf
import Definitions.Def_AlgebraicGeometry_LocalRepresentabilityULift
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSum
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicCurve_RelCartier
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_DescentAction
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible
attribute [-instance] AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal'
attribute [-simp] PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard
  AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian

theorem AlgebraicGeometry.RelPicard.forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsSeparated c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (R' : Type u) [CommRing R'] [Algebra R R'] [Module.Finite R R'] [Algebra.Etale R R']
    [Module.FaithfullyFlat R R']
    (D' : RelativePic0Designation R' (SmoothProperCurve.baseChange R c R'))
    (h' : RepresentsRelSubPic (SmoothProperCurve.baseChange R c R') (SmoothProperCurve.sectionBaseChange R' ε)
      (algEquivZeroCut (SmoothProperCurve.baseChange R c R') (SmoothProperCurve.sectionBaseChange R' ε)) D')
    (hlft : LocallyOfFiniteType D'.toBase)

    {M : ℕ} (B : Fin M → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]
    (z : ∀ i, Spec (CommRingCat.of (B i)) ⟶ C)
    (hz : ∀ i, z i ≫ c = Spec.map (CommRingCat.ofHom (algebraMap R (B i))))

    (deg : Fin M → ℕ) (hdeg : ∀ i, 1 ≤ deg i)
    (σ : ∀ i, Fin (deg i) → SchemeHomOver (𝟙 (Spec (CommRingCat.of R'))) (SmoothProperCurve.baseChange R c R'))
    (hσ : ∀ i m, ∃ y : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of (B i)),
      (σ i m).1 ≫ pullback.fst c (SmoothProperCurve.specMap R R') = y ≫ z i)

    (r g : ℕ) {ι : Type u}
    (idx : {a : Fin (r - g) → Fin M // Function.Injective a} → (∀ i, Fin (deg i)) → ι)
    (X : ι → Scheme.{u})
    (f : ∀ i, uliftYoneda.{u + 1}.obj (X i) ⟶
      (relSubPicPresheaf (SmoothProperCurve.baseChange R c R') (SmoothProperCurve.sectionBaseChange R' ε)
        (algEquivZeroCut (SmoothProperCurve.baseChange R c R') (SmoothProperCurve.sectionBaseChange R' ε))).overTotal)
    (hf : ∀ i, MorphismProperty.presheafULift.{u + 1} @IsOpenImmersion (f i))
    (hfin : ∀ (i : ι) (F : Finset (X i)), ∃ U : (X i).Opens, IsAffineOpen U ∧ ∀ x ∈ F, x ∈ U)
    (Dγ : ι → RelEffCartierDiv (SmoothProperCurve.baseChange R c R') (r - g) (𝟙 (Spec (CommRingCat.of R'))))
    (hDγ : ∀ (a : {a : Fin (r - g) → Fin M // Function.Injective a}) (m : ∀ i, Fin (deg i)),
      (Dγ (idx a m)).I = prodKerGraph (SmoothProperCurve.baseChange R c R')
        (fun j => (σ (a.1 j) (m (a.1 j))).1) (fun j => (σ (a.1 j) (m (a.1 j))).2))

    (hεinv : ∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ Spec (CommRingCat.of R')),
      (sectionIdeal (SmoothProperCurve.baseChange R c R') (SmoothProperCurve.sectionBaseChange R' ε) t).IsInvertible)
    (hTw : ∀ ⦃T T' : Scheme.{u}⦄ {t : T ⟶ Spec (CommRingCat.of R')} {t' : T' ⟶ Spec (CommRingCat.of R')}
      (ψ : SchemeHomOver t' t),
      Nonempty ((Scheme.Modules.pullback (baseChangeSnd (SmoothProperCurve.baseChange R c R') ψ)).obj
        (sectionTwist (SmoothProperCurve.baseChange R c R') (SmoothProperCurve.sectionBaseChange R' ε) t r) ≅
        sectionTwist (SmoothProperCurve.baseChange R c R') (SmoothProperCurve.sectionBaseChange R' ε) t' r))
    (hDγinv : ∀ (i : ι) ⦃T : Scheme.{u}⦄ (t : T ⟶ Spec (CommRingCat.of R')),
      ((Dγ i).pullbackAlong t (Category.comp_id t)).I.IsInvertible)

    (hmem : ∀ (i : ι) ⦃T : Scheme.{u}⦄
      (x : uliftYoneda.{u + 1}.obj T ⟶
        (relSubPicPresheaf (SmoothProperCurve.baseChange R c R') (SmoothProperCurve.sectionBaseChange R' ε)
          (algEquivZeroCut (SmoothProperCurve.baseChange R c R') (SmoothProperCurve.sectionBaseChange R' ε))).overTotal),
      LocallyOfFiniteType (uliftYonedaEquiv x).1 →
      ∀ (L : RigidifiedLineBundle (SmoothProperCurve.baseChange R c R') (SmoothProperCurve.sectionBaseChange R' ε)
        (uliftYonedaEquiv x).1), Quotient.mk _ L = (uliftYonedaEquiv x).2.1 →
      ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T),
        (∀ (𝒲 : (pullback (pullback.snd (SmoothProperCurve.baseChange R c R') (uliftYonedaEquiv x).1) s).TwoAffineOpenCover),
          Subsingleton (𝒲.sectionsOf (fibreAt (SmoothProperCurve.baseChange R c R') (uliftYonedaEquiv x).1 s)
            (fibreModule (SmoothProperCurve.baseChange R c R') (uliftYonedaEquiv x).1 s
            (L.L ⊗ (sectionTwist (SmoothProperCurve.baseChange R c R') (SmoothProperCurve.sectionBaseChange R' ε)
              (uliftYonedaEquiv x).1 r ⊗
              ((Dγ i).pullbackAlong (uliftYonedaEquiv x).1 (Category.comp_id _)).idealModule)))).H1) →
        ∃ φ' : Spec (CommRingCat.of k) ⟶ X i,
          uliftYoneda.{u + 1}.map φ' ≫ f i = uliftYoneda.{u + 1}.map s ≫ x)

    (hgp : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra R Ω]
      (L₀ : (pullback c (SmoothProperCurve.specMap R Ω)).Modules), Scheme.Modules.IsInvertible L₀ →
      IsAlgEquivZero (pullback.snd c (SmoothProperCurve.specMap R Ω)) L₀ →
      ∃ a : Fin (r - g) → Fin M, Function.Injective a ∧
        ∀ v : Fin (r - g) → {q : Spec (CommRingCat.of Ω) ⟶ pullback c (SmoothProperCurve.specMap R Ω) //
            q ≫ pullback.snd c (SmoothProperCurve.specMap R Ω) = 𝟙 _},
          (∀ j, ∃ ψ : B (a j) →ₐ[R] Ω,
            (v j).1 ≫ pullback.fst c (SmoothProperCurve.specMap R Ω) =
              Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ z (a j)) →
          ∀ 𝒲 : (pullback c (SmoothProperCurve.specMap R Ω)).TwoAffineOpenCover,
            Subsingleton (𝒲.sectionsOf (pullback.snd c (SmoothProperCurve.specMap R Ω))
              (L₀ ⊗ ((((sectionFibrePoint ε (SmoothProperCurve.specMap R Ω)).1.ker) ^ r).invModule ⊗
                (∏ j, (v j).1.ker).module))).H1) :
    ∀ x : D'.P, ∃ W : D'.P.Opens, IsAffineOpen W ∧
      ∀ r : ↑(pullback (D'.toBase ≫ SmoothProperCurve.specMap R R') (SmoothProperCurve.specMap R R')),
        (pullback.fst (D'.toBase ≫ SmoothProperCurve.specMap R R') (SmoothProperCurve.specMap R R')) r = x →
        (DescentAction.ofRepresentableBy (SmoothProperCurve.specMap R R')
          (relSubPicPresheaf c ε (algEquivZeroCut c ε)) D'.toBase
          (AlgebraicGeometry.RelPicard.BaseChange.representableByRestrict c ε R' h')).act r ∈ W := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible.solution
