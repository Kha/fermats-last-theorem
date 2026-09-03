import Definitions.Def_GaloisRep_Flat
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import P2M.Util
import P2M.Sol.S_RibetIrr_isFlatAt_of_linearEquiv_baseChange
attribute [-instance] instIsScalarTowerTensorProduct_definitions
attribute [-simp] closureCounit_apply genericFibreAlgHom_tmul tensorInclusion_closureComul coe_closureAntipode_apply tensorToGenericFibre_tmul tensorInclusion_tmul mem_flatClosure_iff

open scoped TensorProduct

theorem RibetIrr.isFlatAt_of_linearEquiv_baseChange
    {𝒪' : Type} [CommRing 𝒪'] [IsDomain 𝒪'] [IsDiscreteValuationRing 𝒪']
    (K : Type) [Field K] [Algebra 𝒪' K] [IsFractionRing 𝒪' K]
    (ρ₁ ρ₂ : GaloisRepAdic 𝒪') (p : ℕ)
    (e : (K ⊗[𝒪'] ρ₁.V) ≃ₗ[K] (K ⊗[𝒪'] ρ₂.V))
    (he : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (v : K ⊗[𝒪'] ρ₁.V),
      e ((ρ₁.ρ σ).baseChange K v) = (ρ₂.ρ σ).baseChange K (e v))
    (hflat₂ : ρ₂.IsFlatAt p) :
    ρ₁.IsFlatAt p := by p2m_exact_reverting @_root_.P2MW.S_RibetIrr_isFlatAt_of_linearEquiv_baseChange.solution
