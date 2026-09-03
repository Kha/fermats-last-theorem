import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import Definitions.Def_Dieudonne_WittGroupHopf
import Definitions.Def_HopfAlgebra_HopfIdealQuotient
import Definitions.Def_Dieudonne_WittKernelHopf
import P2M.Util
import P2M.Sol.S_Deformation_WittKernel_addSubgroup_eq_top_and_exists_addMonoidHom_apply_tautoClass_eq_of_pow_eq
attribute [-instance] MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra HopfAlgebra.IsHopfTower.refl
attribute [-simp] CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply ModpDieudonneRealization.mk.sizeOf_spec ModpDieudonneRealization.mk.injEq CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul HopfAlgebra.HopfTower.quotientMap_mk HopfAlgebra.IsHopfSubalgebra.ι₂_comulK HopfAlgebra.IsHopfTower.toBialgHom_apply HopfAlgebra.IsHopfTower.reprMap_right HopfAlgebra.IsHopfSubalgebra.counitK_apply HopfAlgebra.IsHopfSubalgebra.coe_antipodeK HopfAlgebra.HopfTower.galoisInv_tmul HopfAlgebra.HopfTower.galoisFwd_tmul HopfAlgebra.mem_augIdeal HopfAlgebra.IsHopfTower.reprMap_index HopfAlgebra.HopfTower.antipodeAlgHom_apply HopfAlgebra.IsHopfTower.reprMap_left HopfAlgebra.IsHopfSubalgebra.ι₂_tmul
attribute [-simp] HopfAlgebra.HopfTower.θ₁_tmul HopfAlgebra.HopfTower.fwdB_apply HopfAlgebra.HopfTower.invQuot_mk HopfAlgebra.HopfTower.translateEquiv_apply HopfAlgebra.HopfTower.θ₂_tmul HopfAlgebra.IsHopfSubalgebra.ι₃_tmul

universe v w

theorem Deformation.WittKernel.addSubgroup_eq_top_and_exists_addMonoidHom_apply_tautoClass_eq_of_pow_eq
    (p : ℕ) [Fact p.Prime] (n a b : ℕ) (hab : a < b) (J : Type v) [Finite J]
    {D : Type w} [AddCommGroup D] (MD : Deformation.DieudonneDatum (p : ℤ) D)
    (hV : MD.V ^ n = 0) (hF : MD.F ^ b = MD.F ^ a) (d : J → D) :
    (∀ N : AddSubgroup (Deformation.DieudonneModule (ZMod p) p
        (Deformation.WittKernel.Coord (ZMod p) p n a b J)),
      (∀ z ∈ N, Deformation.DieudonneModule.frobenius (ZMod p) p _ z ∈ N) →
      (∀ z ∈ N, Deformation.DieudonneModule.verschiebung (ZMod p) p _ z ∈ N) →
      (∀ j, Deformation.WittKernel.tautoClass (ZMod p) p n a b J j ∈ N) → N = ⊤) ∧
    ∃ ρ : Deformation.DieudonneModule (ZMod p) p (Deformation.WittKernel.Coord (ZMod p) p n a b J) →+ D,
      (∀ z, ρ (Deformation.DieudonneModule.frobenius (ZMod p) p _ z) = MD.F (ρ z)) ∧
      (∀ z, ρ (Deformation.DieudonneModule.verschiebung (ZMod p) p _ z) = MD.V (ρ z)) ∧
      ∀ j, ρ (Deformation.WittKernel.tautoClass (ZMod p) p n a b J j) = d j := by p2m_exact_reverting @_root_.P2MW.S_Deformation_WittKernel_addSubgroup_eq_top_and_exists_addMonoidHom_apply_tautoClass_eq_of_pow_eq.solution
