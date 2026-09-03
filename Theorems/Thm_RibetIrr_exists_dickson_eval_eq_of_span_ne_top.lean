import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.Polynomial.Dickson
import Definitions.Def_GaloisRep_Adic
import P2M.Util
import P2M.Sol.S_RibetIrr_exists_dickson_eval_eq_of_span_ne_top
attribute [-instance] AlgebraicClosure.Rat.isGalois
attribute [-simp] Deformation.matrixRepresentation_apply

open Polynomial

open scoped TensorProduct

theorem RibetIrr.exists_dickson_eval_eq_of_span_ne_top
    (p : ℕ) [Fact p.Prime] (N : ℕ)
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] [Finite (IsLocalRing.ResidueField 𝒪)]
    [CharZero 𝒪]
    (K : Type) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]
    (ρ : GaloisRepAdic 𝒪) (hp : (p : 𝒪) ∈ IsLocalRing.maximalIdeal 𝒪) (hN : N ≠ 0)
    (hunr : ∀ q : ℕ, q.Prime → ¬ q ∣ N → q ≠ p → ρ.IsUnramifiedAt q)
    (hloc : ∀ (L : Type) [Field L] [Algebra 𝒪 L] [Algebra K L] [IsScalarTower 𝒪 K L]
      [FiniteDimensional K L] (W : Submodule L (L ⊗[𝒪] ρ.V)), Module.finrank L W = 1 →
      (∀ σ, ∀ w ∈ W, (ρ.ρ σ).baseChange L w ∈ W) →
      (∃ n : ℕ, 0 < n ∧ ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime p →
          ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ w ∈ W, ((ρ.ρ σ).baseChange L ^ n) w = w) ∨
        (∃ n : ℕ, 0 < n ∧ ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime p →
          ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ v, ((ρ.ρ σ).baseChange L ^ n) v - v ∈ W))
    (a : ℕ → 𝒪) (E₀ : Finset ℕ)
    (hfrob : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ E₀ →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
          LinearMap.charpoly (ρ.ρ σ) = X ^ 2 - C (a ℓ) * X + C ((ℓ : 𝒪)))
    (hspan : Submodule.span K (Set.range fun σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ =>
      (ρ.ρ σ).baseChange K) ≠ ⊤) :
    ∃ m : ℕ, m ≠ 0 ∧ ∃ E : Finset ℕ, ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ E →
      (dickson 1 ((ℓ : 𝒪)) m).eval (a ℓ) = (ℓ : 𝒪) ^ m + 1 := by p2m_exact_reverting @_root_.P2MW.S_RibetIrr_exists_dickson_eval_eq_of_span_ne_top.solution
