import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import P2M.Util
import P2M.Sol.S_PDivisibleGroup_exists_bialgHom_comp_transition_eq_nsmulBialgHom_and_injective_and_map_ker_counit_eq_torsionIdeal_and_faithfullyFlat
attribute [-instance] PDivisibleGroup.Points.instAddCommGroup PDivisibleGroup.Points.instInhabited PDivisibleGroup.Point.instCommGroup PDivisibleGroup.pointsDirectedSystem PDivisibleGroup.Points.instDistribMulAction PDivisibleGroup.Point.instCommMonoid TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instFinite
attribute [-simp] PDivisibleGroup.Tower.levelCast_rfl PDivisibleGroup.Tower.transitionLE_one PDivisibleGroup.Tower.transitionLE_zero PDivisibleGroup.Hopf.nsmulBialgHom_apply PDivisibleGroup.Points.smul_pointsMkAdd PDivisibleGroup.pointsMkAdd_pointInclLE PDivisibleGroup.Point.toAlgHom_ofAlgHom PDivisibleGroup.pointsMkAdd_pointIncl PDivisibleGroup.pointsMk_pointInclLE PDivisibleGroup.pointIncl_apply PDivisibleGroup.pointInclLE_self PDivisibleGroup.toAlgHom_pointMap PDivisibleGroup.Point.toConv_ofConv PDivisibleGroup.Hopf.antipodeAlgHom_apply PDivisibleGroup.Hopf.convCompMonoidHom_apply PDivisibleGroup.pointsMap_pointsMkAdd PDivisibleGroup.Point.ofAlgHom_toAlgHom PDivisibleGroup.pointsMk_pointIncl PDivisibleGroup.Point.ofConv_toConv TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply FreyPackage.mk.sizeOf_spec
attribute [-simp] FreyPackage.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul

set_option autoImplicit false

theorem PDivisibleGroup.exists_bialgHom_comp_transition_eq_nsmulBialgHom_and_injective_and_map_ker_counit_eq_torsionIdeal_and_faithfullyFlat
    {R : Type} [CommRing R] [IsLocalRing R] (p : ℕ) [Fact p.Prime] {h : ℕ} (G : PDivisibleGroup R p h) (w : ℕ) :
    ∃ m : G.level w →ₐc[R] G.level (w + 1),
      (m : G.level w →ₐ[R] G.level (w + 1)).comp (G.transitionAlgHom w) =
        PDivisibleGroup.Hopf.nsmulAlgHom R (G.level (w + 1)) p ∧
      (G.transitionAlgHom w).comp (m : G.level w →ₐ[R] G.level (w + 1)) =
        PDivisibleGroup.Hopf.nsmulAlgHom R (G.level w) p ∧
      Function.Injective m ∧
      Ideal.map (m : G.level w →ₐ[R] G.level (w + 1)) (PDivisibleGroup.Hopf.augIdeal R (G.level w)) =
        PDivisibleGroup.Hopf.torsionIdeal R (G.level (w + 1)) p ∧

      (letI := (m : G.level w →ₐ[R] G.level (w + 1)).toRingHom.toAlgebra
       Module.FaithfullyFlat (G.level w) (G.level (w + 1))) := by p2m_exact_reverting @_root_.P2MW.S_PDivisibleGroup_exists_bialgHom_comp_transition_eq_nsmulBialgHom_and_injective_and_map_ker_counit_eq_torsionIdeal_and_faithfullyFlat.solution
