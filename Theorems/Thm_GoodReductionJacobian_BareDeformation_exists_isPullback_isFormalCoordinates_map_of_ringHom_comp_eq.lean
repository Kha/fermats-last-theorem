import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_GoodReductionJacobian_BareDeformation
import Definitions.Def_MvFormalGroup_Deformation
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_BareDeformation_exists_isPullback_isFormalCoordinates_map_of_ringHom_comp_eq
attribute [-simp] GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst
attribute [-simp] RegularLocalRingQuotientAscent.dualNumberFst_apply

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld IsLocalRing
open scoped TensorProduct
theorem GoodReductionJacobian.BareDeformation.exists_isPullback_isFormalCoordinates_map_of_ringHom_comp_eq
    (B' B B₁ : Type) [CommRing B'] [CommRing B] [CommRing B₁] [Algebra B' B₁] [Algebra B B₁]
    (φ : B' →+* B) (hφ : (algebraMap B B₁).comp φ = algebraMap B' B₁)
    {A₁ : Scheme.{0}} {f₁ : A₁ ⟶ Spec (CommRingCat.of B₁)} {L₁ : RelativeGroupLaw B₁ f₁}
    {d : ℕ} (Ĝ₁ : MvFormalGroup d B₁) (θ₁ : RelativeGroupLaw.FormalCoordinates f₁ d)
    (P : BareDeformation f₁ L₁ B')
    (GP : MvFormalGroup.Deformation Ĝ₁ B') (θP : RelativeGroupLaw.FormalCoordinates P.f d)
    (hθP : P.L.IsFormalCoordinates GP.F θP) (hlP : P.LiftsCoordinates θ₁ θP) :
    ∃ (D : BareDeformation f₁ L₁ B) (h : D.A ⟶ P.A)
      (hc : IsPullback h D.f P.f (Spec.map (CommRingCat.ofHom φ))),
      D.g ≫ h = P.g ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (x y : SchemeHomOver t D.f),
        (D.L.mul t x y).1 ≫ h =
          (P.L.mul (t ≫ Spec.map (CommRingCat.ofHom φ))
            ⟨x.1 ≫ h, by rw [Category.assoc, hc.w, ← Category.assoc, x.2]⟩
            ⟨y.1 ≫ h, by rw [Category.assoc, hc.w, ← Category.assoc, y.2]⟩).1) ∧
      ∃ (G : MvFormalGroup.Deformation Ĝ₁ B) (θ : RelativeGroupLaw.FormalCoordinates D.f d),
        G.F = GP.F.map φ ∧
        (GP.F.IsComm → G.F.IsComm) ∧
        D.L.IsFormalCoordinates G.F θ ∧ D.LiftsCoordinates θ₁ θ ∧
        ∀ (B'' : Type) [CommRing B''] [Algebra B B''] (s : Fin d → B''), (∀ i, IsNilpotent (s i)) →
          letI : Algebra B' B'' := ((algebraMap B B'').comp φ).toAlgebra
          (θ B'' s).1 ≫ h = (θP B'' s).1 := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_BareDeformation_exists_isPullback_isFormalCoordinates_map_of_ringHom_comp_eq.solution
