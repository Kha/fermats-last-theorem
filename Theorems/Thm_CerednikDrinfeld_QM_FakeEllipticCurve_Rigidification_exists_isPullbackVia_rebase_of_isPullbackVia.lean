import Definitions.Def_CerednikDrinfeld_QMRigidification
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_isPullbackVia_rebase_of_isPullbackVia
attribute [-simp] GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst
attribute [-simp] RegularLocalRingQuotientAscent.dualNumberFst_apply

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian

theorem CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_isPullbackVia_rebase_of_isPullbackVia
    {r N : ℕ}
    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪)
    (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr] (σ : Onr →ₐ[𝒪] Onr)
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b])
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (A₀r : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π})) (prA : A₀r.A ⟶ A₀.A)
    (F : A₀.A ⟶ A₀r.A) (V : A₀r.A ⟶ A₀.A)
    (B : Type) [CommRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B) (E : FakeEllipticCurve Λ N B)
    (ρ : FakeEllipticCurve.Rigidification r π A₀ ψ E) (ρp : FakeEllipticCurve.Rigidification r π A₀ (ψ.comp σ) E)
    (ub : ρ.Eb.A ⟶ ρp.Eb.A) (hub : ub ≫ ρp.gb = ρ.gb) (hub' : ub ≫ ρp.Eb.f = ρ.Eb.f)
    (gA' : ρp.Ab.A ⟶ A₀r.A) (hgA' : FakeEllipticCurve.IsPullbackVia (FakeEllipticCurve.Rigidification.residueLeg π ψ) A₀r ρp.Ab gA')
    (hgA'' : gA' ≫ prA = ρp.gA)
    (Fb : ρ.Ab.A ⟶ ρp.Ab.A) (hFb : Fb ≫ gA' = ρ.gA ≫ F) (hFb' : Fb ≫ ρp.Ab.f = ρ.Ab.f)
    (Vb : ρp.Ab.A ⟶ ρ.Ab.A) (hVb : Vb ≫ ρ.gA = gA' ≫ V) (hVb' : Vb ≫ ρ.Ab.f = ρp.Ab.f)
    (hd : ρp.d = ρ.d + 1) (hφ : ub ≫ ρp.φ = ρ.φ ≫ Fb) (hφ' : ρp.φ' = Vb ≫ ρ.φ' ≫ ub)
    (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (φ : B →ₐ[𝒪] B')
    (E' : FakeEllipticCurve Λ N B') (g : E'.A ⟶ E.A) (hg : FakeEllipticCurve.IsPullbackVia (φ : B →+* B') E E' g) :
    ∃ (ρL : FakeEllipticCurve.Rigidification r π A₀ (φ.comp ψ) E')
      (ρpL : FakeEllipticCurve.Rigidification r π A₀ (φ.comp (ψ.comp σ)) E')
      (_ : FakeEllipticCurve.Rigidification.IsPullbackVia φ g hg ρ ρL)
      (_ : FakeEllipticCurve.Rigidification.IsPullbackVia φ g hg ρp ρpL)
      (ubL : ρL.Eb.A ⟶ ρpL.Eb.A) (_ : ubL ≫ ρpL.gb = ρL.gb) (_ : ubL ≫ ρpL.Eb.f = ρL.Eb.f)
      (gA'L : ρpL.Ab.A ⟶ A₀r.A)
      (_ : FakeEllipticCurve.IsPullbackVia (FakeEllipticCurve.Rigidification.residueLeg π (φ.comp ψ)) A₀r ρpL.Ab gA'L)
      (_ : gA'L ≫ prA = ρpL.gA)
      (FbL : ρL.Ab.A ⟶ ρpL.Ab.A) (_ : FbL ≫ gA'L = ρL.gA ≫ F) (_ : FbL ≫ ρpL.Ab.f = ρL.Ab.f)
      (VbL : ρpL.Ab.A ⟶ ρL.Ab.A) (_ : VbL ≫ ρL.gA = gA'L ≫ V) (_ : VbL ≫ ρL.Ab.f = ρpL.Ab.f),
      ρpL.d = ρL.d + 1 ∧ ubL ≫ ρpL.φ = ρL.φ ≫ FbL ∧ ρpL.φ' = VbL ≫ ρL.φ' ≫ ubL := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_isPullbackVia_rebase_of_isPullbackVia.solution
