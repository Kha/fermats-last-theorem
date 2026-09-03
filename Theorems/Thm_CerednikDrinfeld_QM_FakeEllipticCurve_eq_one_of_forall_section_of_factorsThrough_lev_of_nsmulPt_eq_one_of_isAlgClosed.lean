import Definitions.Def_CerednikDrinfeld_QMModuli
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_eq_one_of_forall_section_of_factorsThrough_lev_of_nsmulPt_eq_one_of_isAlgClosed
attribute [-instance] GoodReductionJacobian.RelativeGroupLaw.isIso_endKerStr_schemeHomOverId
attribute [-simp] CerednikDrinfeld.QM.FakeEllipticCurve.FullLevel.mk.sizeOf_spec CerednikDrinfeld.QM.FakeEllipticCurve.FullLevel.mk.injEq CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.mk.injEq CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.mk.sizeOf_spec GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase
attribute [-simp] GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe NeronModelInfra.schemeHomOverNpow_succ NeronModelInfra.schemeHomOverNpow_zero

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion
theorem CerednikDrinfeld.QM.FakeEllipticCurve.eq_one_of_forall_section_of_factorsThrough_lev_of_nsmulPt_eq_one_of_isAlgClosed
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (k₀ : Type) [Field k₀] [IsAlgClosed k₀] (E : FakeEllipticCurve Λ N k₀) (n : ℕ) (hn : (n : k₀) ≠ 0)
    {ι : Type} (g : ι → (E.A ⟶ E.A)) (hg : ∀ i, g i ≫ E.f = E.f)
    (hyp : ∀ Q₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k₀))) E.f,
      FactorsThrough E.lev Q₀ →
      nsmulPt E.L (𝟙 (Spec (CommRingCat.of k₀))) n Q₀ = E.L.one (𝟙 (Spec (CommRingCat.of k₀))) →
      (∀ i, mapPt (g i) (hg i) Q₀ = E.L.one (𝟙 (Spec (CommRingCat.of k₀)))) →
      Q₀ = E.L.one (𝟙 (Spec (CommRingCat.of k₀))))
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k₀)) (P : SchemeHomOver t E.f)
    (hlev : FactorsThrough E.lev P) (hP : nsmulPt E.L t n P = E.L.one t)
    (hgP : ∀ i, mapPt (g i) (hg i) P = E.L.one t) :
    P = E.L.one t := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_eq_one_of_forall_section_of_factorsThrough_lev_of_nsmulPt_eq_one_of_isAlgClosed.solution
