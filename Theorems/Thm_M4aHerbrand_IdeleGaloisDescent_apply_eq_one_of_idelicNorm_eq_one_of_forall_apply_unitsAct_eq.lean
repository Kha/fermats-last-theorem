import Definitions.Def_M4aHerbrand_GenuineDescent
import P2M.Util
import P2M.Sol.S_M4aHerbrand_IdeleGaloisDescent_apply_eq_one_of_idelicNorm_eq_one_of_forall_apply_unitsAct_eq
attribute [-instance] M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup
attribute [-simp] M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk M4aHerbrand.IdeleGaloisDescent.classAct_mk GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl NumberField.SUnits.val_zsmul NumberField.SUnits.val_add Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk

set_option autoImplicit false

open NumberField

theorem M4aHerbrand.IdeleGaloisDescent.apply_eq_one_of_idelicNorm_eq_one_of_forall_apply_unitsAct_eq
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    {M : Type*} [CommGroup M] (ξ : (AdeleRing (𝓞 L) L)ˣ →* M)
    (hξ : ∀ z : (AdeleRing (𝓞 L) L)ˣ, ξ (D.unitsAct σ z) = ξ z)
    (n : (AdeleRing (𝓞 L) L)ˣ) (hn : (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm n = 1) :
    ξ n = 1 := by p2m_exact_reverting @_root_.P2MW.S_M4aHerbrand_IdeleGaloisDescent_apply_eq_one_of_idelicNorm_eq_one_of_forall_apply_unitsAct_eq.solution
