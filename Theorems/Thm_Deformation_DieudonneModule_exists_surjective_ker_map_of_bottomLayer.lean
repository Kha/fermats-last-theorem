import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_GaloisRep_RatLocalizedAtResidue
import Definitions.Def_HopfAlgebra_CartierDualInstances
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import P2M.Util
import P2M.Sol.S_Deformation_DieudonneModule_exists_surjective_ker_map_of_bottomLayer
attribute [-instance] HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra CartierDual.instAlgebraBaseChangeDual CartierDual.instRingBaseChangeDual CartierDual.instModuleRestrictBaseChange CartierDual.instIsScalarTowerRestrictBaseChange instIsScalarTowerTensorProduct_definitions HopfAlgebra.IsHopfTower.refl
attribute [-simp] HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul HopfOrder.doubleCmp_tmul HopfOrder.tensorSqHom_tmul HopfOrder.baseChangeHom_tmul HopfAlgebra.FVectStructure.addChar_apply HopfAlgebra.FVectStructure.mk.sizeOf_spec HopfAlgebra.FVectStructure.mk.injEq HopfAlgebra.FVectStructure.unitsAct_apply HopfAlgebra.mem_vanishingIdealOfPoints_iff HopfAlgebra.liftPoint_mk HopfAlgebra.mem_ptSet_iff CartierDual.dualBaseChangeLin_tmul CartierDual.dualBaseChange_tmul mem_flatClosure_iff CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply HopfAlgebra.HopfTower.quotientMap_mk HopfAlgebra.IsHopfSubalgebra.ι₂_comulK HopfAlgebra.IsHopfTower.toBialgHom_apply HopfAlgebra.IsHopfTower.reprMap_right HopfAlgebra.IsHopfSubalgebra.counitK_apply HopfAlgebra.IsHopfSubalgebra.coe_antipodeK HopfAlgebra.HopfTower.galoisInv_tmul HopfAlgebra.HopfTower.galoisFwd_tmul HopfAlgebra.mem_augIdeal HopfAlgebra.IsHopfTower.reprMap_index
attribute [-simp] HopfAlgebra.HopfTower.antipodeAlgHom_apply HopfAlgebra.IsHopfTower.reprMap_left HopfAlgebra.IsHopfSubalgebra.ι₂_tmul HopfAlgebra.HopfTower.θ₁_tmul HopfAlgebra.HopfTower.fwdB_apply HopfAlgebra.HopfTower.invQuot_mk HopfAlgebra.HopfTower.translateEquiv_apply HopfAlgebra.HopfTower.θ₂_tmul HopfAlgebra.IsHopfSubalgebra.ι₃_tmul ModpDieudonneRealization.mk.sizeOf_spec ModpDieudonneRealization.mk.injEq

set_option autoImplicit false
open scoped TensorProduct in

theorem Deformation.DieudonneModule.exists_surjective_ker_map_of_bottomLayer
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt p) H]
    [Module.Finite (GaloisRep.ratLocalizedAt p) H] [Module.Free (GaloisRep.ratLocalizedAt p) H]
    [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H]
    (hloc : IsLocalRing H) (hdual : IsLocalRing (CartierDual (GaloisRep.ratLocalizedAt p) H))
    {κ : Type} [Field κ] [Finite κ] [CharP κ p]
    {N : Type} [AddCommGroup N] [Module κ N] [Module.Finite κ N]
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (N →ₗ[κ] N))
    (e : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃ N)
    (he_add : ∀ f g, e (f * g) = e f + e g)
    (he_gal : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
      (∀ h : H, g h = σ (f h)) → e g = ρ σ (e f))
    (θ : κ → (H →ₐc[GaloisRep.ratLocalizedAt p] H))
    (hθ : ∀ (a : κ) (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
      (∀ h : H, g h = f (θ a h)) → e g = a • e f)
    (V : Submodule κ N)
    (hV : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), ∀ x ∈ V, ρ σ x ∈ V)
    (HV : Type) [CommRing HV] [HopfAlgebra (GaloisRep.ratLocalizedAt p) HV]
    [Module.Finite (GaloisRep.ratLocalizedAt p) HV] [Module.Free (GaloisRep.ratLocalizedAt p) HV]
    [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) HV]
    (π : H →ₐc[GaloisRep.ratLocalizedAt p] HV) (hπ : Function.Surjective π)
    (eV : WithConv (HV →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃ ↥V)
    (heV : ∀ f : WithConv (HV →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
      ((eV f : ↥V) : N) =
        e (WithConv.toConv ((WithConv.ofConv f).comp (π : H →ₐ[GaloisRep.ratLocalizedAt p] HV))))
    (θV : κ → (HV →ₐc[GaloisRep.ratLocalizedAt p] HV))
    (hθV : ∀ a : κ,
      (θV a : HV →ₐ[GaloisRep.ratLocalizedAt p] HV).comp (π : H →ₐ[GaloisRep.ratLocalizedAt p] HV) =
        (π : H →ₐ[GaloisRep.ratLocalizedAt p] HV).comp (θ a : H →ₐ[GaloisRep.ratLocalizedAt p] H))
    (hbot : V ≠ ⊤ →
      ∃ (V' : Submodule κ (N ⧸ V)) (ι : ↥V ≃ₗ[κ] ↥V'),
        (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), ∀ x ∈ V',
          Submodule.mapQ V V (ρ σ) (fun y hy => hV σ y hy) x ∈ V') ∧
        ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (v : ↥V),
          ((ι ⟨ρ σ v, hV σ v v.2⟩ : ↥V') : N ⧸ V) =
            Submodule.mapQ V V (ρ σ) (fun y hy => hV σ y hy) ((ι v : ↥V') : N ⧸ V))
    (hVtop : V ≠ ⊤) :
    ∃ lam : ↥(AddMonoidHom.ker (Deformation.DieudonneModule.map (ZMod p) p
          (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) π))) →+
        Deformation.DieudonneModule (ZMod p) p ((ZMod p) ⊗[GaloisRep.ratLocalizedAt p] HV),
      Function.Surjective lam ∧
      (∀ x (hx : Deformation.DieudonneModule.frobenius (ZMod p) p _ x.1 ∈
          AddMonoidHom.ker (Deformation.DieudonneModule.map (ZMod p) p
            (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) π))),
        lam ⟨_, hx⟩ = Deformation.DieudonneModule.frobenius (ZMod p) p _ (lam x)) ∧
      (∀ x (hx : Deformation.DieudonneModule.verschiebung (ZMod p) p _ x.1 ∈
          AddMonoidHom.ker (Deformation.DieudonneModule.map (ZMod p) p
            (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) π))),
        lam ⟨_, hx⟩ = Deformation.DieudonneModule.verschiebung (ZMod p) p _ (lam x)) ∧
      (∀ (a : κ) x (hx : Deformation.DieudonneModule.map (ZMod p) p
            (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (θ a)) x.1 ∈
          AddMonoidHom.ker (Deformation.DieudonneModule.map (ZMod p) p
            (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) π))),
        lam ⟨_, hx⟩ = Deformation.DieudonneModule.map (ZMod p) p
          (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (θV a)) (lam x)) := by p2m_exact_reverting @_root_.P2MW.S_Deformation_DieudonneModule_exists_surjective_ker_map_of_bottomLayer.solution
