import Mathlib
import Definitions.Def_GaloisRep_Residual
import P2M.Util
import P2M.Sol.S_ResidualGaloisRep_exists_index_two_stable_line_of_trace_frobenius_eq_zero_of_modEq_two
attribute [-instance] AlgebraicClosure.Rat.isGalois FrobeniusDensity.isMaximal_ratPrimeIdeal FrobeniusDensity.liesOver_ratBelow
attribute [-simp] TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec

set_option autoImplicit false

theorem ResidualGaloisRep.exists_index_two_stable_line_of_trace_frobenius_eq_zero_of_modEq_two
    (k : Type) [Field k] [CharP k 3] (ρbar : ResidualGaloisRep k)
    (n : ℕ → ℤ) (S : Set ℕ) (hS : S.Finite)
    (htr : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
          LinearMap.trace k ρbar.V (ρbar.ρ σ) = (n ℓ : k))
    (h0 : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S → ℓ ≡ 2 [MOD 3] → (n ℓ : k) = 0) :
    ¬ ∀ (K : Type) [Field K] [Algebra k K]
      (G : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)), G.index = 2 →
        ∀ V : Submodule K (ρbar.baseChange K).V,
          (∀ σ ∈ G, ∀ x ∈ V, (ρbar.baseChange K).ρ σ x ∈ V) → V = ⊥ ∨ V = ⊤ := by p2m_exact_reverting @_root_.P2MW.S_ResidualGaloisRep_exists_index_two_stable_line_of_trace_frobenius_eq_zero_of_modEq_two.solution
