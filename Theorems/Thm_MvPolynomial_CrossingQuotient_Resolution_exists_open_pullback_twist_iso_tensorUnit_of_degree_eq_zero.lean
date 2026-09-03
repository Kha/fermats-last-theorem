import Mathlib
import Definitions.Def_MvPolynomial_CrossingResolutionScheme
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicCurve_RelCartier
import P2M.Util
import P2M.Sol.S_MvPolynomial_CrossingQuotient_Resolution_exists_open_pullback_twist_iso_tensorUnit_of_degree_eq_zero
attribute [-instance] AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial SheafOfModules.isIso_ihomModelToIhom
attribute [-simp] AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry MvPolynomial MvPolynomial.CrossingQuotient

theorem MvPolynomial.CrossingQuotient.Resolution.exists_open_pullback_twist_iso_tensorUnit_of_degree_eq_zero
    {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O)
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {ϖ}) (e : ℕ) (he : 1 ≤ e)
    {X : Scheme.{u}} (πX : X ⟶ Spec (CommRingCat.of O)) [IsSeparated πX] (x : X) (U : X.Opens) (hxU : x ∈ U)
    (f : (U : Scheme.{u}) ⟶ crossingScheme (ϖ ^ e)) [LocallyOfFiniteType f] [FormallyUnramified f]
    (hf : f ≫ Spec.map (CommRingCat.ofHom (algebraMap O (CrossingQuotient O (ϖ ^ e)))) = U.ι ≫ πX)
    (f_mem_Vc_iff : ∀ y : U,
      f.base y ∈ ((PrimeSpectrum.basicOpen (CrossingQuotient.U (ϖ ^ e)) : (crossingScheme (ϖ ^ e)).Opens) ⊔
        (PrimeSpectrum.basicOpen (CrossingQuotient.V (ϖ ^ e)) : (crossingScheme (ϖ ^ e)).Opens)) ↔ (y : X) ≠ x)
    (hinj : ∀ y y' : ↥(pullback f (Resolution.toCrossing ϖ e)),
      ((pullback.fst f (Resolution.toCrossing ϖ e)).base y).1 = x →
        ((pullback.fst f (Resolution.toCrossing ϖ e)).base y').1 = x →
          (pullback.snd f (Resolution.toCrossing ϖ e)).base y = (pullback.snd f (Resolution.toCrossing ϖ e)).base y' → y = y')
    [IsIntegral (pullback f (Resolution.toCrossing ϖ e))]
    (hgen : ∃ y : ↥(pullback f (Resolution.toCrossing ϖ e)),
      (pullback.fst f (Resolution.toCrossing ϖ e) ≫ U.ι ≫ πX).base y ≠ IsLocalRing.closedPoint O)
    (Fc : Fin (e + 1) → (Resolution ϖ e).IdealSheafData) (hFc_inv : ∀ k, (Fc k).IsInvertible)
    (hFc_t : ∏ k, Fc k = Scheme.IdealSheafData.ofIdealTop (Ideal.span
      {(Resolution.toSpec ϖ e).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom ϖ)}))
    (hFc_u : ∏ k, Fc k ^ (k : ℕ) = Scheme.IdealSheafData.ofIdealTop (Ideal.span
      {(Resolution.toCrossing ϖ e).appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of (CrossingQuotient O (ϖ ^ e)))).inv.hom (CrossingQuotient.U (ϖ ^ e)))}))
    (hFc_supp : ∀ (k : Fin (e + 1)) (z : ↥(Resolution ϖ e)), z ∈ (Fc k).support →
      (Resolution.toSpec ϖ e).base z = IsLocalRing.closedPoint O)
    (hFc_vertex : ∀ (k : ℕ) (hk0 : 0 < k) (hke : k < e) (z : ↥(Resolution ϖ e)), z ∈ (Fc ⟨k, by omega⟩).support →
      CrossingQuotient.U (ϖ ^ e) ∈ ((Resolution.toCrossing ϖ e).base z).asIdeal ∧
        CrossingQuotient.V (ϖ ^ e) ∈ ((Resolution.toCrossing ϖ e).base z).asIdeal)
    (hFc_node : ∀ (k : ℕ) (hke : k < e), ∃ z : ↥(Resolution ϖ e),
      z ∈ (Fc ⟨k, by omega⟩).support ∧ z ∈ (Fc ⟨k + 1, by omega⟩).support)
    (hFc_sect : ∀ (t : Spec (CommRingCat.of O) ⟶ Resolution ϖ e), t ≫ Resolution.toSpec ϖ e = 𝟙 _ →
      ∀ (dd : ℕ) (hd0 : 0 < dd) (hde : dd < e), t.base (IsLocalRing.closedPoint O) ∈ (Fc ⟨dd, by omega⟩).support →
      (∀ k : Fin (e + 1), (k : ℕ) ≠ dd → t.base (IsLocalRing.closedPoint O) ∉ (Fc k).support) →
      IsClosedImmersion t ∧ (t.ker).IsInvertible ∧
        ∃ rr : CrossingQuotient O (ϖ ^ e), t.ker * ∏ k, Fc k ^ (min (k : ℕ) dd) =
          Scheme.IdealSheafData.ofIdealTop (Ideal.span {(Resolution.toCrossing ϖ e).appTop.hom
            ((Scheme.ΓSpecIso (CommRingCat.of (CrossingQuotient O (ϖ ^ e)))).inv.hom rr)}))
    {m : ℕ} (σ : Fin m → (Spec (CommRingCat.of O) ⟶ pullback f (Resolution.toCrossing ϖ e)))
    (hσ : ∀ j, σ j ≫ pullback.fst f (Resolution.toCrossing ϖ e) ≫ U.ι ≫ πX = 𝟙 _)
    (pos neg : Fin m → ℕ) (d : Fin m → ℕ) (hd : ∀ j, 0 < d j ∧ d j < e)
    (hσd : ∀ j, (σ j).base (IsLocalRing.closedPoint O) ∈
        ((Fc ⟨d j, (hd j).2.trans e.lt_succ_self⟩).comap (pullback.snd f (Resolution.toCrossing ϖ e))).support ∧
      ∀ k : Fin (e + 1), (k : ℕ) ≠ d j →
        (σ j).base (IsLocalRing.closedPoint O) ∉ ((Fc k).comap (pullback.snd f (Resolution.toCrossing ϖ e))).support)
    (vp vn : Fin (e + 1) → ℕ)
    {r : ℕ} (J : Fin r → (pullback f (Resolution.toCrossing ϖ e)).IdealSheafData) (hJ : ∀ i, (J i).IsInvertible)
    (hJs : ∀ i, ((J i).support : Set _) ∩
      (pullback.fst f (Resolution.toCrossing ϖ e) ≫ U.ι ≫ πX).base ⁻¹' {IsLocalRing.closedPoint O} = ∅)
    (jp jn : Fin r → ℕ)
    (hdeg : ∀ k : ℕ, ∀ hk0 : 0 < k, ∀ hke : k < e,
      (∑ j, if d j = k then ((pos j : ℤ) - neg j) else 0) +
        (((vp ⟨k - 1, by omega⟩ : ℤ) - vn ⟨k - 1, by omega⟩) - 2 * ((vp ⟨k, by omega⟩ : ℤ) - vn ⟨k, by omega⟩) +
          ((vp ⟨k + 1, by omega⟩ : ℤ) - vn ⟨k + 1, by omega⟩)) = 0) :
    ∃ V : X.Opens, x ∈ V ∧ V ≤ U ∧
      Nonempty ((Scheme.Modules.pullback
          (pullback.fst f (Resolution.toCrossing ϖ e) ⁻¹ᵁ (U.ι ⁻¹ᵁ V)).ι).obj
            ((List.finRange m).foldr (fun j M => ((((σ j).ker) ^ pos j).invModule ⊗ (((σ j).ker) ^ neg j).module) ⊗ M)
              ((List.finRange r).foldr (fun i M => (((J i) ^ jp i).invModule ⊗ ((J i) ^ jn i).module) ⊗ M)
                ((∏ k, (Fc k).comap (pullback.snd f (Resolution.toCrossing ϖ e)) ^ vp k).invModule ⊗
                  (∏ k, (Fc k).comap (pullback.snd f (Resolution.toCrossing ϖ e)) ^ vn k).module))) ≅
        𝟙_ _) := by p2m_exact_reverting @_root_.P2MW.S_MvPolynomial_CrossingQuotient_Resolution_exists_open_pullback_twist_iso_tensorUnit_of_degree_eq_zero.solution
