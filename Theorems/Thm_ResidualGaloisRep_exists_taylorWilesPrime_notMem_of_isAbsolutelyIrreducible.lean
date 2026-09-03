import Mathlib
import Definitions.Def_GaloisRep_Residual
import P2M.Util
import P2M.Sol.S_ResidualGaloisRep_exists_taylorWilesPrime_notMem_of_isAbsolutelyIrreducible
attribute [-instance] FrobeniusDensity.isMaximal_ratPrimeIdeal FrobeniusDensity.liesOver_ratBelow AlgebraicClosure.Rat.isGalois
attribute [-simp] TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec TaylorWiles.CyclotomicLevelStructure.mk.sizeOf_spec TaylorWiles.CyclotomicLevelStructure.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq

set_option autoImplicit false

open Polynomial

theorem ResidualGaloisRep.exists_taylorWilesPrime_notMem_of_isAbsolutelyIrreducible
    {k : Type} [Field k] (h2 : (2 : k) ≠ 0) (ρbar : ResidualGaloisRep k)
    (habs : ρbar.IsAbsolutelyIrreducible)
    (hsplit : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      ∃ α β : k, LinearMap.charpoly (ρbar.ρ σ) = (X - C α) * (X - C β))
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (n : ℕ) (S : Finset ℕ) :
    ∃ q : ℕ, q.Prime ∧ q ∉ S ∧ q ≡ 1 [MOD p ^ n] ∧ ρbar.IsUnramifiedAt q ∧
      ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime q →
        ∀ φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt φ q →
          ∃ α β : k, α ≠ β ∧ LinearMap.charpoly (ρbar.ρ φ) = (X - C α) * (X - C β) := by p2m_exact_reverting @_root_.P2MW.S_ResidualGaloisRep_exists_taylorWilesPrime_notMem_of_isAbsolutelyIrreducible.solution
