import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_forall_apply_comp_eq_smul_of_finrank_eq_prime_pow_of_ne_two
attribute [-instance] HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra CartierDual.instAlgebraBaseChangeDual CartierDual.instRingBaseChangeDual CartierDual.instModuleRestrictBaseChange CartierDual.instIsScalarTowerRestrictBaseChange MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra instIsScalarTowerTensorProduct_definitions GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy WeierstrassCurve.Affine.Point.instFinite
attribute [-simp] HopfOrder.doubleCmp_tmul HopfOrder.tensorSqHom_tmul HopfOrder.baseChangeHom_tmul HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul HopfAlgebra.FVectStructure.addChar_apply HopfAlgebra.FVectStructure.mk.sizeOf_spec HopfAlgebra.FVectStructure.mk.injEq HopfAlgebra.FVectStructure.unitsAct_apply HopfAlgebra.mem_vanishingIdealOfPoints_iff HopfAlgebra.liftPoint_mk HopfAlgebra.mem_ptSet_iff CartierDual.dualBaseChangeLin_tmul CartierDual.dualBaseChange_tmul CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply mem_flatClosure_iff GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ResidualGaloisRep.Equiv.mk.sizeOf_spec
attribute [-simp] ResidualGaloisRep.Equiv.mk.injEq

set_option autoImplicit false

open scoped PadicInt

theorem HopfAlgebra.exists_forall_apply_comp_eq_smul_of_finrank_eq_prime_pow_of_ne_two
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    {k : Type} [Field k] {M : Type} [AddCommGroup M] [Module k M]
    [DistribMulAction (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) M]
    [SMulCommClass (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) k M]
    (H : Type) [CommRing H] [HopfAlgebra ℤ_[p] H] [Module.Finite ℤ_[p] H] [Module.Free ℤ_[p] H]
    [Coalgebra.IsCocomm ℤ_[p] H] (hrank : ∃ a : ℕ, Module.finrank ℤ_[p] H = p ^ a)
    (e : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p) ≃ M)
    (he_add : ∀ f g, e (f * g) = e f + e g)
    (he_act : ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
      (f g : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p)), (∀ x : H, g x = σ (f x)) → e g = σ • (e f)) :
    ∃ θ : k → (H →ₐc[ℤ_[p]] H),
      (∀ (a : k) (f : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p)),
        e (WithConv.toConv ((WithConv.ofConv f).comp (θ a : H →ₐ[ℤ_[p]] H))) = a • e f) ∧
      (∀ (a : k) (g : H →ₐc[ℤ_[p]] H),
        (∀ f : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p),
          e (WithConv.toConv ((WithConv.ofConv f).comp (g : H →ₐ[ℤ_[p]] H))) = a • e f) → g = θ a) ∧
      (∀ a b : k, θ (a * b) = (θ a).comp (θ b)) ∧
      θ 1 = BialgHom.id ℤ_[p] H ∧
      (∀ a b : k, WithConv.toConv (θ (a + b) : H →ₐ[ℤ_[p]] H) =
        WithConv.toConv (θ a : H →ₐ[ℤ_[p]] H) * WithConv.toConv (θ b : H →ₐ[ℤ_[p]] H)) ∧
      WithConv.toConv (θ 0 : H →ₐ[ℤ_[p]] H) = 1 := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_forall_apply_comp_eq_smul_of_finrank_eq_prime_pow_of_ne_two.solution
