import Definitions.Def_AlgebraicGeometry_ThetaGroupLaw
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianSchemeOfType
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_isAlgClosed_principalRoot_thetaPt_of_rootedSymmetricOfType
attribute [-instance] PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback
attribute [-simp] AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec
attribute [-simp] AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped BigOperators MonoidalCategory

theorem AlgebraicGeometry.PolarisedAbelianScheme.exists_isAlgClosed_principalRoot_thetaPt_of_rootedSymmetricOfType
    {g d n : ℕ} (δ : Fin g → ℕ) [∀ i, NeZero (δ i)] (hδd : ∏ i, δ i = d)
    {S : Type} [CommRing S] (hd : IsUnit ((d : ℕ) : S))
    (u : PolarisedAbelianScheme g d n S) (hu : PolarisedAbelianScheme.RootedSymmetricOfType δ S u)
    {K : Type} [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of S))
    (x : (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))) → SchemeHomOver t u.f)
    (hx0 : x 0 = u.L.one t) (hx : ∀ h h' : (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))), x (h + h') = u.L.mul t (x h) (x h'))
    (hxinj : Function.Injective x)
    (hxK : ∀ y : SchemeHomOver t u.f, Polarisation.MemKernel u.f u.L u.pol t y → ∃ h : (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))), y = x h)
    (θ₀ : (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))) → ThetaPt u.f u.L u.pol t) (hθ₀ : ∀ h, (θ₀ h).pt = x h)
    (θ : ThetaPt u.f u.L u.pol t)
    (hcomm : ∀ (h : (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i)))) (s : Γ((Scheme.Modules.pullback (pullback.fst u.f t)).obj u.pol, ⊤)),
      θ.act ((θ₀ h).act s) = (θ₀ h).act (θ.act s)) :
    ∃ (L : Type) (_ : Field L) (_ : IsAlgClosed L) (ψ : K →+* L), Epi (Spec.map (CommRingCat.ofHom ψ)) ∧
    ∃ (L' : RelativeGroupLaw L (pullback.snd u.f (Spec.map (CommRingCat.ofHom ψ) ≫ t)))
      (_ : ∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of L)) (P Q : SchemeHomOver t' (pullback.snd u.f (Spec.map (CommRingCat.ofHom ψ) ≫ t))),
        (L'.mul t' P Q).1 ≫ pullback.fst u.f (Spec.map (CommRingCat.ofHom ψ) ≫ t) =
          (u.L.mul (t' ≫ (Spec.map (CommRingCat.ofHom ψ) ≫ t))
            ⟨P.1 ≫ pullback.fst u.f (Spec.map (CommRingCat.ofHom ψ) ≫ t), by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ pullback.fst u.f (Spec.map (CommRingCat.ofHom ψ) ≫ t), by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1)
      (𝓛₀ : (pullback u.f (Spec.map (CommRingCat.ofHom ψ) ≫ t)).Modules) (a b : ℕ),
      1 ≤ a + b ∧ Scheme.Modules.IsInvertible 𝓛₀ ∧
      Polarisation.KernelTrivial (pullback.snd u.f (Spec.map (CommRingCat.ofHom ψ) ≫ t)) L' 𝓛₀ ∧
      Polarisation.LocIsoOnBase (pullback.snd u.f (Spec.map (CommRingCat.ofHom ψ) ≫ t))
        ((Scheme.Modules.pullback (pullback.fst u.f (Spec.map (CommRingCat.ofHom ψ) ≫ t))).obj u.pol)
        (Scheme.Modules.tpow 𝓛₀ a ⊗ Scheme.Modules.tpow ((Scheme.Modules.pullback (Polarisation.negMor (pullback.snd u.f (Spec.map (CommRingCat.ofHom ψ) ≫ t)) L')).obj 𝓛₀) b) ∧
    ∃ (xL : (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))) → SchemeHomOver (Spec.map (CommRingCat.ofHom ψ) ≫ t) u.f)
      (θL : (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))) → ThetaPt u.f u.L u.pol (Spec.map (CommRingCat.ofHom ψ) ≫ t)) (θ' : ThetaPt u.f u.L u.pol (Spec.map (CommRingCat.ofHom ψ) ≫ t)),
      (∀ h, (xL h).1 = Spec.map (CommRingCat.ofHom ψ) ≫ (x h).1) ∧
      xL 0 = u.L.one _ ∧ (∀ h h' : (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))), xL (h + h') = u.L.mul _ (xL h) (xL h')) ∧ Function.Injective xL ∧
      (∀ y : SchemeHomOver (Spec.map (CommRingCat.ofHom ψ) ≫ t) u.f, Polarisation.MemKernel u.f u.L u.pol _ y → ∃ h, y = xL h) ∧
      (∀ h, (θL h).pt = xL h) ∧ (θ'.pt.1 = Spec.map (CommRingCat.ofHom ψ) ≫ θ.pt.1) ∧
      (∀ (h : (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i)))) (s : Γ((Scheme.Modules.pullback (pullback.fst u.f (Spec.map (CommRingCat.ofHom ψ) ≫ t))).obj u.pol, ⊤)), θ'.act ((θL h).act s) = (θL h).act (θ'.act s)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_isAlgClosed_principalRoot_thetaPt_of_rootedSymmetricOfType.solution
