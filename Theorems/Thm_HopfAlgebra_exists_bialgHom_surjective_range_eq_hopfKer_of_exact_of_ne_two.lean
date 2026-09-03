import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_HopfAlgebra_HopfKer
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_bialgHom_surjective_range_eq_hopfKer_of_exact_of_ne_two
attribute [-instance] HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra CartierDual.instAlgebraBaseChangeDual CartierDual.instRingBaseChangeDual CartierDual.instModuleRestrictBaseChange CartierDual.instIsScalarTowerRestrictBaseChange MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra instIsScalarTowerTensorProduct_definitions GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy WeierstrassCurve.Affine.Point.instFinite
attribute [-simp] HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul HopfOrder.doubleCmp_tmul HopfOrder.tensorSqHom_tmul HopfOrder.baseChangeHom_tmul HopfAlgebra.FVectStructure.addChar_apply HopfAlgebra.FVectStructure.mk.sizeOf_spec HopfAlgebra.FVectStructure.mk.injEq HopfAlgebra.FVectStructure.unitsAct_apply HopfAlgebra.mem_vanishingIdealOfPoints_iff HopfAlgebra.liftPoint_mk HopfAlgebra.mem_ptSet_iff CartierDual.dualBaseChangeLin_tmul CartierDual.dualBaseChange_tmul CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply mem_flatClosure_iff GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq

set_option autoImplicit false

open scoped PadicInt

theorem HopfAlgebra.exists_bialgHom_surjective_range_eq_hopfKer_of_exact_of_ne_two
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    {M₁ M₂ M₃ : Type} [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃]
    [DistribMulAction (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) M₁]
    [DistribMulAction (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) M₂]
    [DistribMulAction (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) M₃]
    (α : M₁ →+ M₂) (β : M₂ →+ M₃)
    (hα : ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (m : M₁), α (σ • m) = σ • α m)
    (hβ : ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (m : M₂), β (σ • m) = σ • β m)
    (hαi : Function.Injective α) (hβs : Function.Surjective β) (hex : Function.Exact α β)
    (H₁ : Type) [CommRing H₁] [HopfAlgebra ℤ_[p] H₁] [Module.Finite ℤ_[p] H₁] [Module.Free ℤ_[p] H₁]
    [Coalgebra.IsCocomm ℤ_[p] H₁] (hrank₁ : ∃ a : ℕ, Module.finrank ℤ_[p] H₁ = p ^ a)
    (e₁ : WithConv (H₁ →ₐ[ℤ_[p]] PadicAlgCl p) ≃ M₁)
    (he₁_add : ∀ f g, e₁ (f * g) = e₁ f + e₁ g)
    (he₁_act : ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
      (f g : WithConv (H₁ →ₐ[ℤ_[p]] PadicAlgCl p)), (∀ x : H₁, g x = σ (f x)) → e₁ g = σ • e₁ f)
    (H₂ : Type) [CommRing H₂] [HopfAlgebra ℤ_[p] H₂] [Module.Finite ℤ_[p] H₂] [Module.Free ℤ_[p] H₂]
    [Coalgebra.IsCocomm ℤ_[p] H₂] (hrank₂ : ∃ a : ℕ, Module.finrank ℤ_[p] H₂ = p ^ a)
    (e₂ : WithConv (H₂ →ₐ[ℤ_[p]] PadicAlgCl p) ≃ M₂)
    (he₂_add : ∀ f g, e₂ (f * g) = e₂ f + e₂ g)
    (he₂_act : ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
      (f g : WithConv (H₂ →ₐ[ℤ_[p]] PadicAlgCl p)), (∀ x : H₂, g x = σ (f x)) → e₂ g = σ • e₂ f)
    (H₃ : Type) [CommRing H₃] [HopfAlgebra ℤ_[p] H₃] [Module.Finite ℤ_[p] H₃] [Module.Free ℤ_[p] H₃]
    [Coalgebra.IsCocomm ℤ_[p] H₃] (hrank₃ : ∃ a : ℕ, Module.finrank ℤ_[p] H₃ = p ^ a)
    (e₃ : WithConv (H₃ →ₐ[ℤ_[p]] PadicAlgCl p) ≃ M₃)
    (he₃_add : ∀ f g, e₃ (f * g) = e₃ f + e₃ g)
    (he₃_act : ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
      (f g : WithConv (H₃ →ₐ[ℤ_[p]] PadicAlgCl p)), (∀ x : H₃, g x = σ (f x)) → e₃ g = σ • e₃ f) :
    ∃ (π : H₂ →ₐc[ℤ_[p]] H₁) (j : H₃ →ₐc[ℤ_[p]] H₂),
      (∀ f : WithConv (H₁ →ₐ[ℤ_[p]] PadicAlgCl p),
        e₂ (WithConv.toConv ((WithConv.ofConv f).comp (π : H₂ →ₐ[ℤ_[p]] H₁))) = α (e₁ f)) ∧
      (∀ f : WithConv (H₂ →ₐ[ℤ_[p]] PadicAlgCl p),
        e₃ (WithConv.toConv ((WithConv.ofConv f).comp (j : H₃ →ₐ[ℤ_[p]] H₂))) = β (e₂ f)) ∧
      Function.Surjective π ∧ Function.Injective j ∧
      (j : H₃ →ₐ[ℤ_[p]] H₂).range = HopfAlgebra.hopfKer π := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_bialgHom_surjective_range_eq_hopfKer_of_exact_of_ne_two.solution
