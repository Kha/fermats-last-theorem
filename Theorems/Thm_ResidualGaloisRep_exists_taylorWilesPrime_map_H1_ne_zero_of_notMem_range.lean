import Mathlib
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_ExtEndgame_ProductionDatum
import P2M.Util
import P2M.Sol.S_ResidualGaloisRep_exists_taylorWilesPrime_map_H1_ne_zero_of_notMem_range
attribute [-instance] FrobeniusDensity.isMaximal_ratPrimeIdeal FrobeniusDensity.liesOver_ratBelow instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete
attribute [-simp] TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec

set_option autoImplicit false

open Polynomial CategoryTheory groupCohomology ExtCitation

theorem ResidualGaloisRep.exists_taylorWilesPrime_map_H1_ne_zero_of_notMem_range
    {k : Type} [Field k] (ρbar : ResidualGaloisRep k)
    {p : ℕ} [Fact p.Prime] {n : ℕ} {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ (p ^ n))
    {R : Type} [CommRing R] (M : Rep R (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (hM : ∃ E : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ E ∧
      ∀ s ∈ E.fixingSubgroup, M.ρ s = 1)
    (c : cocycles₁ M)
    (hc : ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ g s, s ∈ F.fixingSubgroup → c (g * s) = c g)
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσζ : σ ζ = ζ)
    {α β : k} (hαβ : α ≠ β) (hσ : LinearMap.charpoly (ρbar.ρ σ) = (X - C α) * (X - C β))
    (hcσ : c σ ∉ LinearMap.range (M.ρ σ - 1))
    (T : Finset ℕ) :
    ∃ q : Nat.Primes, (q : ℕ) ∉ T ∧ (q : ℕ) ≡ 1 [MOD p ^ n] ∧ ρbar.IsUnramifiedAt q ∧
      (∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime q →
        ∀ φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt φ q →
          ∃ α β : k, α ≠ β ∧ LinearMap.charpoly (ρbar.ρ φ) = (X - C α) * (X - C β)) ∧
      (groupCohomology.map (primeLocalToGlobal q)
          (𝟙 (Rep.res (primeLocalToGlobal q) M)) 1).hom (H1π M c) ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_ResidualGaloisRep_exists_taylorWilesPrime_map_H1_ne_zero_of_notMem_range.solution
