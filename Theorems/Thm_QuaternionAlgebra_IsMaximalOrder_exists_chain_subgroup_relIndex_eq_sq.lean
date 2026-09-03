import Mathlib
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_IsMaximalOrder_exists_chain_subgroup_relIndex_eq_sq
attribute [-simp] QuaternionAlgebra.ClassSet.map_mk QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.mk.injEq CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.mk.sizeOf_spec CerednikDrinfeld.ShimuraCurveModel.ModuliWitness.mk.injEq CerednikDrinfeld.QM.mapPt_coe CerednikDrinfeld.QM.FakeEllipticCurve.mk.injEq CerednikDrinfeld.QM.FakeEllipticCurve.mk.sizeOf_spec CerednikDrinfeld.ShimuraCurveModel.ModuliWitness.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver

set_option autoImplicit false

open scoped Quaternion
open QuaternionAlgebra
theorem QuaternionAlgebra.IsMaximalOrder.exists_chain_subgroup_relIndex_eq_sq
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    {G : Type*} [CommGroup G] (ρ : ↥Λ → G →* G)
    (hρ_one : ∀ h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ, ρ ⟨1, h1⟩ = MonoidHom.id G)
    (hρ_mul : ∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
      ρ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = (ρ x).comp (ρ y))
    (hρ_add : ∀ (x y : ↥Λ) (g : G), ρ (x + y) g = ρ x g * ρ y g)
    (N : Subgroup G) (hN : (N : Set G).Finite) (hstab : ∀ (x : ↥Λ) (g : G), g ∈ N → ρ x g ∈ N) :
    ∃ (e : ℕ) (ℓ : Fin e → ℕ) (H : Fin (e + 1) → Subgroup G),
      (∀ j, (ℓ j).Prime) ∧ H 0 = ⊥ ∧ H (Fin.last e) = N ∧
      (∀ j : Fin e, H j.castSucc ≤ H j.succ) ∧
      (∀ (j : Fin (e + 1)) (x : ↥Λ) (g : G), g ∈ H j → ρ x g ∈ H j) ∧
      (∀ j : Fin e, (H j.castSucc).relIndex (H j.succ) = ℓ j ^ 2) ∧
      (∀ (j : Fin e) (g : G), g ∈ H j.succ → g ^ (ℓ j) ∈ H j.castSucc) ∧
      (∀ j : Fin e, (ℓ j = q ∨ ℓ j = q') → ∀ g : G, g ∈ H j.succ →
        ∀ (m : ↥Λ) (k : ℤ), (m : ℍ[ℚ, a, b]) * star (m : ℍ[ℚ, a, b]) = (((ℓ j : ℤ) * k : ℚ) : ℍ[ℚ, a, b]) →
          ρ m g ∈ H j.castSucc) ∧
      Nat.card N = ∏ j, ℓ j ^ 2 := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_chain_subgroup_relIndex_eq_sq.solution
