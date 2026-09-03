import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_QuaternionAlgebra_QMPeriodLattice
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_factorsThrough_levK_symm_iff_exists_qmPeriodMap_mul_eq_of_forall_geomPoint
attribute [-simp] GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField Pointwise
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian

theorem CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.factorsThrough_levK_symm_iff_exists_qmPeriodMap_mul_eq_of_forall_geomPoint
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) {N : ℕ} (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ)
    (E : FakeEllipticCurve Λ N ℂ)

    (latt : Submodule ℤ (Fin 2 → ℂ))
    (e : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f ≃ ((Fin 2 → ℂ) ⧸ latt.toAddSubgroup))
    (hE1 : ∀ P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f,
      e (E.L.mul (𝟙 (Spec (CommRingCat.of ℂ))) P Q) = e P + e Q)
    (hE2 : ∀ (x : ↥Λ) (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f) (v : Fin 2 → ℂ),
      e P = (v : (Fin 2 → ℂ) ⧸ latt.toAddSubgroup) →
      e (pushPt (E.act x) (E.act_over x) P) =
        ((((ι (x : ℍ[ℚ, a, b])).map (algebraMap ℝ ℂ)).mulVec v : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ latt.toAddSubgroup))

    (m ℓ : ℕ) (hm : m ≠ 0) (hℓ : ℓ ≠ 0) (hℓm : ℓ ∣ m) (P : E.FullLevel m)
    (τ : UpperHalfPlane) (c : ℂ) (hc : c ≠ 0) (hlatt : c • latt = qmPeriodLattice ι Λ τ)
    (w : ℍ[ℚ, a, b]) (vP : Fin 2 → ℂ) (hvP : e P.P = (vP : (Fin 2 → ℂ) ⧸ latt.toAddSubgroup))
    (hcvP : c • vP = ((m : ℂ)⁻¹) • qmPeriodMap ι τ w)

    (L₀ : Submodule ℤ ℍ[ℚ, a, b]) (t : ℍ[ℚ, a, b])
    (hLT : ∀ y : ℍ[ℚ, a, b], (∃ z ∈ Λ, z * t = y) ↔ ∃ z ∈ Λ, ∃ x ∈ Λ, x ∈ L₀ ∧ (ℓ : ℚ) • z + x * w = y)

    (K : E.ExtraLevel ℓ)
    (hK : ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : ℂ →+* k) (Q : SchemeHomOver (geomPoint k sk) E.f),
      FactorsThrough K.levK Q ↔
        ∃ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ ∧
          pushPt (E.act x) (E.act_over x)
            (nsmulPt E.L (geomPoint k sk) (m / ℓ) (FakeEllipticCurve.sectionAt P.P k sk)) = Q)
    (v : Fin 2 → ℂ) :
    FactorsThrough K.levK (e.symm (v : (Fin 2 → ℂ) ⧸ latt.toAddSubgroup)) ↔
      ∃ y ∈ Λ, qmPeriodMap ι τ (y * t) = (c * (ℓ : ℂ)) • v := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_factorsThrough_levK_symm_iff_exists_qmPeriodMap_mul_eq_of_forall_geomPoint.solution
