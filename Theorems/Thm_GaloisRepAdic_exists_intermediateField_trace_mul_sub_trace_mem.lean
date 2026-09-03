import Mathlib
import Definitions.Def_GaloisRep_Adic
import P2M.Util
import P2M.Sol.S_GaloisRepAdic_exists_intermediateField_trace_mul_sub_trace_mem

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open IsLocalRing

theorem GaloisRepAdic.exists_intermediateField_trace_mul_sub_trace_mem
    {R : Type} [CommRing R] [IsLocalRing R] (ρ : GaloisRepAdic R)
    (J : Ideal R) (hJ : ∃ m : ℕ, maximalIdeal R ^ m ≤ J) :
    ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ σ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ F, τ x = x) →
        ρ.trace (σ * τ) - ρ.trace σ ∈ J := by p2m_exact_reverting @_root_.P2MW.S_GaloisRepAdic_exists_intermediateField_trace_mul_sub_trace_mem.solution
