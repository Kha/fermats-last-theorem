import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Definitions.Def_GaloisRep_Flat
import P2M.Util
import P2M.Sol.S_RibetIrr_line_fixed_or_quotient_fixed_by_inertia_of_isFlatAt
attribute [-instance] MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra AlgebraicClosure.Rat.isGalois instIsScalarTowerTensorProduct_definitions
attribute [-simp] CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply closureCounit_apply genericFibreAlgHom_tmul tensorInclusion_closureComul coe_closureAntipode_apply tensorToGenericFibre_tmul tensorInclusion_tmul mem_flatClosure_iff

open scoped TensorProduct

theorem RibetIrr.line_fixed_or_quotient_fixed_by_inertia_of_isFlatAt (p : ℕ) [Fact p.Prime]
    (𝒪' : Type) [CommRing 𝒪'] [IsDomain 𝒪'] [IsDiscreteValuationRing 𝒪']
    (K : Type) [Field K] [Algebra 𝒪' K] [IsFractionRing 𝒪' K]
    (ρ : GaloisRepAdic 𝒪') (hflat : ρ.IsFlatAt p) (hdet : ρ.DetIsCyclotomic p)
    (W : Submodule K (K ⊗[𝒪'] ρ.V)) (hW : Module.finrank K W = 1)
    (hWstab : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), ∀ w ∈ W,
      (ρ.ρ σ).baseChange K w ∈ W) :
    (∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime p →
        ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ w ∈ W, (ρ.ρ σ).baseChange K w = w) ∨
    (∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime p →
        ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ v : K ⊗[𝒪'] ρ.V, (ρ.ρ σ).baseChange K v - v ∈ W) := by p2m_exact_reverting @_root_.P2MW.S_RibetIrr_line_fixed_or_quotient_fixed_by_inertia_of_isFlatAt.solution
