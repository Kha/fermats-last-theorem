import Mathlib
import Definitions.Def_GaloisRep_Flat
import P2M.Util
import P2M.Sol.S_HopfAlgebra_existsUnique_bialgHom_ratLocalizedAt_forall_apply_comp_eq_and_bijective_of_addEquiv_of_ne_two
attribute [-instance] HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra CartierDual.instAlgebraBaseChangeDual CartierDual.instRingBaseChangeDual CartierDual.instModuleRestrictBaseChange CartierDual.instIsScalarTowerRestrictBaseChange MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra instIsScalarTowerTensorProduct_definitions
attribute [-simp] HopfOrder.doubleCmp_tmul HopfOrder.tensorSqHom_tmul HopfOrder.baseChangeHom_tmul HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul HopfAlgebra.FVectStructure.addChar_apply HopfAlgebra.FVectStructure.mk.sizeOf_spec HopfAlgebra.FVectStructure.mk.injEq HopfAlgebra.FVectStructure.unitsAct_apply HopfAlgebra.mem_vanishingIdealOfPoints_iff HopfAlgebra.liftPoint_mk HopfAlgebra.mem_ptSet_iff CartierDual.dualBaseChangeLin_tmul CartierDual.dualBaseChange_tmul CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply mem_flatClosure_iff

set_option autoImplicit false

theorem HopfAlgebra.existsUnique_bialgHom_ratLocalizedAt_forall_apply_comp_eq_and_bijective_of_addEquiv_of_ne_two
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    {M₁ M₂ : Type} [AddCommGroup M₁] [AddCommGroup M₂]
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) M₁]
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) M₂]
    (H₁ : Type) [CommRing H₁] [HopfAlgebra (GaloisRep.ratLocalizedAt p) H₁]
    [Module.Finite (GaloisRep.ratLocalizedAt p) H₁] [Module.Free (GaloisRep.ratLocalizedAt p) H₁]
    [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H₁]
    (hrank₁ : ∃ a : ℕ, Module.finrank (GaloisRep.ratLocalizedAt p) H₁ = p ^ a)
    (e₁ : WithConv (H₁ →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃ M₁)
    (he₁_add : ∀ f g, e₁ (f * g) = e₁ f + e₁ g)
    (he₁_act : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (f g : WithConv (H₁ →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
      (∀ x : H₁, g x = σ (f x)) → e₁ g = σ • e₁ f)
    (H₂ : Type) [CommRing H₂] [HopfAlgebra (GaloisRep.ratLocalizedAt p) H₂]
    [Module.Finite (GaloisRep.ratLocalizedAt p) H₂] [Module.Free (GaloisRep.ratLocalizedAt p) H₂]
    [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H₂]
    (hrank₂ : ∃ a : ℕ, Module.finrank (GaloisRep.ratLocalizedAt p) H₂ = p ^ a)
    (e₂ : WithConv (H₂ →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃ M₂)
    (he₂_add : ∀ f g, e₂ (f * g) = e₂ f + e₂ g)
    (he₂_act : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (f g : WithConv (H₂ →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
      (∀ x : H₂, g x = σ (f x)) → e₂ g = σ • e₂ f)
    (φ : M₁ ≃+ M₂)
    (hφ : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (m : M₁), φ (σ • m) = σ • φ m) :
    (∃! g : H₂ →ₐc[GaloisRep.ratLocalizedAt p] H₁,
      ∀ f : WithConv (H₁ →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
        e₂ (WithConv.toConv ((WithConv.ofConv f).comp (g : H₂ →ₐ[GaloisRep.ratLocalizedAt p] H₁))) = φ (e₁ f)) ∧
    (∀ g : H₂ →ₐc[GaloisRep.ratLocalizedAt p] H₁,
      (∀ f : WithConv (H₁ →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
        e₂ (WithConv.toConv ((WithConv.ofConv f).comp (g : H₂ →ₐ[GaloisRep.ratLocalizedAt p] H₁))) = φ (e₁ f)) →
      Function.Bijective g) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_existsUnique_bialgHom_ratLocalizedAt_forall_apply_comp_eq_and_bijective_of_addEquiv_of_ne_two.solution
