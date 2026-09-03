import Definitions.Def_GaloisRep_Residual
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ResidualGaloisRep_forall_decompositionStable_eq_bot_or_top_of_charpoly_frobenius_map_eq
attribute [-instance] FrobeniusDensity.isMaximal_ratPrimeIdeal AlgebraicClosure.Rat.isGalois FrobeniusDensity.liesOver_ratBelow GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule
attribute [-simp] ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq

theorem ResidualGaloisRep.forall_decompositionStable_eq_bot_or_top_of_charpoly_frobenius_map_eq
    {k k' : Type} [Field k] [Field k'] (e : k →+* k')
    (ρ : ResidualGaloisRep k) (ρ₀ : ResidualGaloisRep k') (p : ℕ) (S : Finset ℕ)
    (hfrob : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt τ ℓ →
          LinearMap.charpoly (ρ₀.ρ τ) = (LinearMap.charpoly (ρ.ρ τ)).map e)
    (hW2 : ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime p →
      ∀ (k'' : Type) (_ : Field k'') (ψ'' : k' →+* k''),
        ∀ L : Submodule k'' (ρ₀.baseChangeAlong ψ'').V,
          (∀ σ ∈ P.decompositionSubgroup ℚ, ∀ v ∈ L, (ρ₀.baseChangeAlong ψ'').ρ σ v ∈ L) →
          L = ⊥ ∨ L = ⊤) :
    ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime p →
      ∀ L : Submodule k ρ.V,
        (∀ σ ∈ P.decompositionSubgroup ℚ, ∀ v ∈ L, ρ.ρ σ v ∈ L) → L = ⊥ ∨ L = ⊤ := by p2m_exact_reverting @_root_.P2MW.S_ResidualGaloisRep_forall_decompositionStable_eq_bot_or_top_of_charpoly_frobenius_map_eq.solution
