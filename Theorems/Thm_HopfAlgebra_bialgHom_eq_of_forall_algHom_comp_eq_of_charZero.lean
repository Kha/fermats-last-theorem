import Mathlib
import Definitions.Def_GaloisRep_Flat
import P2M.Util
import P2M.Sol.S_HopfAlgebra_bialgHom_eq_of_forall_algHom_comp_eq_of_charZero
attribute [-instance] PDivisibleGroup.Points.instAddCommGroup PDivisibleGroup.Points.instInhabited PDivisibleGroup.Point.instCommGroup PDivisibleGroup.pointsDirectedSystem PDivisibleGroup.Points.instDistribMulAction PDivisibleGroup.Point.instCommMonoid PDivisibleGroup.instHopfAlgebra PDivisibleGroup.instModuleFinite PDivisibleGroup.instCommRing PDivisibleGroup.instIsCocomm PDivisibleGroup.instModuleFree PDivisibleGroup.instModuleFlat TateModule.instModule TateModule.instSMul
attribute [-simp] PDivisibleGroup.Points.smul_pointsMkAdd PDivisibleGroup.pointsMkAdd_pointInclLE PDivisibleGroup.Point.toAlgHom_ofAlgHom PDivisibleGroup.pointsMkAdd_pointIncl PDivisibleGroup.pointsMk_pointInclLE PDivisibleGroup.pointIncl_apply PDivisibleGroup.pointInclLE_self PDivisibleGroup.toAlgHom_pointMap PDivisibleGroup.Point.toConv_ofConv PDivisibleGroup.Hopf.antipodeAlgHom_apply PDivisibleGroup.Hopf.convCompMonoidHom_apply PDivisibleGroup.pointsMap_pointsMkAdd PDivisibleGroup.Point.ofAlgHom_toAlgHom PDivisibleGroup.pointsMk_pointIncl PDivisibleGroup.Point.ofConv_toConv PDivisibleGroup.counit_transition PDivisibleGroup.Hopf.nsmulAlgHom_one PDivisibleGroup.Hopf.torsionIdeal_zero PDivisibleGroup.Hopf.nsmulAlgHom_zero_apply PDivisibleGroup.Hopf.torsionIdeal_one PDivisibleGroup.Hopf.counit_nsmulAlgHom PDivisibleGroup.mk.sizeOf_spec PDivisibleGroup.mk.injEq PDivisibleGroup.height_eq TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply

set_option autoImplicit false

theorem HopfAlgebra.bialgHom_eq_of_forall_algHom_comp_eq_of_charZero
    (K : Type) [Field K] [CharZero K] (Kbar : Type) [Field Kbar] [Algebra K Kbar] [IsAlgClosure K Kbar]
    (E₁ : Type) [CommRing E₁] [HopfAlgebra K E₁] [Coalgebra.IsCocomm K E₁] [Module.Finite K E₁]
    (E₂ : Type) [CommRing E₂] [HopfAlgebra K E₂] [Coalgebra.IsCocomm K E₂] [Module.Finite K E₂]
    (ψ ψ' : E₂ →ₐc[K] E₁)
    (h : ∀ f : E₁ →ₐ[K] Kbar, f.comp (ψ : E₂ →ₐ[K] E₁) = f.comp (ψ' : E₂ →ₐ[K] E₁)) :
    ψ = ψ' := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_bialgHom_eq_of_forall_algHom_comp_eq_of_charZero.solution
