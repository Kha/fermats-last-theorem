import Mathlib
import Definitions.Def_HopfAlgebra_HopfKer
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_bialgHom_surjective_points_eq_of_submonoid_of_bijective_evalPoints_of_perfectField
attribute [-instance] HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra CartierDual.instAlgebraBaseChangeDual CartierDual.instRingBaseChangeDual CartierDual.instModuleRestrictBaseChange CartierDual.instIsScalarTowerRestrictBaseChange MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra instIsScalarTowerTensorProduct_definitions
attribute [-simp] HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul HopfAlgebra.mem_vanishingIdealOfPoints_iff HopfAlgebra.liftPoint_mk HopfAlgebra.mem_ptSet_iff CartierDual.dualBaseChangeLin_tmul CartierDual.dualBaseChange_tmul CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply mem_flatClosure_iff

set_option autoImplicit false

open scoped TensorProduct

universe u v

theorem HopfAlgebra.exists_bialgHom_surjective_points_eq_of_submonoid_of_bijective_evalPoints_of_perfectField
    (K : Type u) [Field K] [PerfectField K]
    (A : Type v) [CommRing A] [HopfAlgebra K A] [Module.Finite K A] [Coalgebra.IsCocomm K A]
    [Finite (WithConv (A →ₐ[K] AlgebraicClosure K))]
    (hev : Function.Bijective
      (Algebra.TensorProduct.lift
        (Algebra.ofId (AlgebraicClosure K) (WithConv (A →ₐ[K] AlgebraicClosure K) → AlgebraicClosure K))
        (Pi.algHom K _
          fun ν : WithConv (A →ₐ[K] AlgebraicClosure K) => (WithConv.ofConv ν : A →ₐ[K] AlgebraicClosure K))
        (fun _ _ => Commute.all _ _) :
        AlgebraicClosure K ⊗[K] A →ₐ[AlgebraicClosure K]
          (WithConv (A →ₐ[K] AlgebraicClosure K) → AlgebraicClosure K)))
    (W : Submonoid (WithConv (A →ₐ[K] AlgebraicClosure K)))
    (hW : ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, ∀ ν ∈ W,
      ∀ ν' : WithConv (A →ₐ[K] AlgebraicClosure K),
        (∀ a : A, WithConv.ofConv ν' a = σ (WithConv.ofConv ν a)) → ν' ∈ W) :
    ∃ (Ā : Type v) (_ : CommRing Ā) (_ : HopfAlgebra K Ā) (_ : Coalgebra.IsCocomm K Ā) (_ : Module.Finite K Ā)
      (π : A →ₐc[K] Ā), Function.Surjective π ∧
      (∀ ψ : Ā →ₐ[K] AlgebraicClosure K, WithConv.toConv (ψ.comp (π : A →ₐ[K] Ā)) ∈ W) ∧
      (∀ ν ∈ W, ∃ ψ : Ā →ₐ[K] AlgebraicClosure K, ψ.comp (π : A →ₐ[K] Ā) = WithConv.ofConv ν) ∧
      Module.finrank K Ā = Nat.card ↥W ∧
      (∀ h : ↥(HopfAlgebra.hopfKer π) →ₐ[K] AlgebraicClosure K,
        ∃ ν : WithConv (A →ₐ[K] AlgebraicClosure K), (WithConv.ofConv ν).comp (HopfAlgebra.hopfKer π).val = h) ∧
      (∀ ν ν' : WithConv (A →ₐ[K] AlgebraicClosure K),
        (WithConv.ofConv ν).comp (HopfAlgebra.hopfKer π).val = (WithConv.ofConv ν').comp (HopfAlgebra.hopfKer π).val
          ↔ ∃ w ∈ W, ν' = ν * w) ∧
      Module.finrank K ↥(HopfAlgebra.hopfKer π) * Nat.card ↥W = Module.finrank K A := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_bialgHom_surjective_points_eq_of_submonoid_of_bijective_evalPoints_of_perfectField.solution
