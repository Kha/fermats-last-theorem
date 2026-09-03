import Definitions.Def_GaloisRep_Residual
import P2M.Util
import P2M.Sol.S_ResidualGaloisRep_iSup_range_sub_one_eq_top_and_trace_quotient_eq_zero_of_forall_stable

set_option autoImplicit false

theorem ResidualGaloisRep.iSup_range_sub_one_eq_top_and_trace_quotient_eq_zero_of_forall_stable
    {k : Type} [Field k] (ρ : ResidualGaloisRep k)
    (P : ValuationSubring (AlgebraicClosure ℚ))
    (hirr : ∀ L : Submodule k ρ.V,
      (∀ σ ∈ P.decompositionSubgroup ℚ, ∀ v ∈ L, ρ.ρ σ v ∈ L) → L = ⊥ ∨ L = ⊤)
    (hram : ∃ τ ∈ P.inertiaSubgroupIn ℚ, ρ.ρ τ ≠ 1) :
    (⨆ τ ∈ P.inertiaSubgroupIn ℚ, LinearMap.range (ρ.ρ τ - 1)) = ⊤ ∧
    ∀ E : (ρ.V ⧸ ⨆ τ ∈ P.inertiaSubgroupIn ℚ, LinearMap.range (ρ.ρ τ - 1)) →ₗ[k]
        (ρ.V ⧸ ⨆ τ ∈ P.inertiaSubgroupIn ℚ, LinearMap.range (ρ.ρ τ - 1)),
      LinearMap.trace k _ E = 0 := by p2m_exact_reverting @_root_.P2MW.S_ResidualGaloisRep_iSup_range_sub_one_eq_top_and_trace_quotient_eq_zero_of_forall_stable.solution
