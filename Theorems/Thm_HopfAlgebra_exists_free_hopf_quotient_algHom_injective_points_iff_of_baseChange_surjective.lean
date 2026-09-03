import Mathlib
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_free_hopf_quotient_algHom_injective_points_iff_of_baseChange_surjective
attribute [-instance] HopfAlgebra.HopfIdealQuotient.instIsCocomm HopfAlgebra.HopfIdealQuotient.instBialgebra HopfAlgebra.HopfIdealQuotient.instHopfAlgebra Ideal.isHopfIdeal_bot HopfAlgebra.flat_quotient_bot HopfAlgebra.finiteType_quotient HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra instIsScalarTowerTensorProduct_definitions
attribute [-simp] HopfAlgebra.HopfIdealQuotient.comul_mk HopfAlgebra.antipodeAlgHom_apply HopfAlgebra.quotientFactorBialgHom_apply_mk HopfAlgebra.quotientBialgHom_apply HopfAlgebra.quotientLiftPoint_mk HopfAlgebra.convCompMonoidHom_apply HopfAlgebra.HopfIdealQuotient.antipode_mk HopfAlgebra.HopfIdealQuotient.counit_mk HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul mem_flatClosure_iff closureCounit_apply genericFibreAlgHom_tmul tensorInclusion_closureComul coe_closureAntipode_apply tensorToGenericFibre_tmul tensorInclusion_tmul

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
set_option Elab.async false

open scoped TensorProduct

theorem HopfAlgebra.exists_free_hopf_quotient_algHom_injective_points_iff_of_baseChange_surjective
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [IsPrincipalIdealRing 𝒪]
    (K : Type) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]
    (A : Type) [CommRing A] [HopfAlgebra 𝒪 A] [Coalgebra.IsCocomm 𝒪 A] [Module.Finite 𝒪 A]
    [Module.Free 𝒪 A]
    (C : Type) [CommRing C] [HopfAlgebra K C] [Algebra 𝒪 C] [IsScalarTower 𝒪 K C]
    (πK : K ⊗[𝒪] A →ₐc[K] C) (hπK : Function.Surjective πK) :
    ∃ (B : Type) (_ : CommRing B) (_ : HopfAlgebra 𝒪 B) (_ : Coalgebra.IsCocomm 𝒪 B)
      (_ : Module.Finite 𝒪 B) (_ : Module.Free 𝒪 B)
      (π : A →ₐc[𝒪] B) (ι : B →ₐ[𝒪] C),
      Function.Surjective π ∧
      Function.Injective ι ∧
      (∀ a : A, ι (π a) = πK ((1 : K) ⊗ₜ[𝒪] a)) ∧
      ∀ (Ω : Type) [CommRing Ω] [Algebra 𝒪 Ω] [Algebra K Ω] [IsScalarTower 𝒪 K Ω]
        (g : A →ₐ[𝒪] Ω),
        (∃ g' : B →ₐ[𝒪] Ω, g'.comp (π : A →ₐ[𝒪] B) = g) ↔
          ∃ g'' : C →ₐ[K] Ω, ∀ a : A, g'' (πK ((1 : K) ⊗ₜ[𝒪] a)) = g a := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_free_hopf_quotient_algHom_injective_points_iff_of_baseChange_surjective.solution
