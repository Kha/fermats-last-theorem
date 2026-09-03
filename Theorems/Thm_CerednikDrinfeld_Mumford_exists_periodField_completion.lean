import Definitions.Def_CerednikDrinfeld_MumfordUniformization
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Mumford_exists_periodField_completion
attribute [-instance] AlgebraicClosure.Rat.isGalois

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.Mumford ModularCurve

theorem CerednikDrinfeld.Mumford.exists_periodField_completion
    (r : ℕ) [Fact r.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime r) :
    ∃ K : IntermediateField ℚ A.valuation.Completion, ∃ ord : Additive (↥K)ˣ →+ ℤ,
      (∀ k : (↥K)ˣ, Valued.v (((k : ↥K) : A.valuation.Completion)) =
        Valued.v ((r : ℕ) : A.valuation.Completion) ^ (ord (Additive.ofMul k))) ∧
      (∀ σ : ↥(A.decompositionSubgroup ℚ),
        (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ A.inertiaSubgroupIn ℚ →
        ∀ s : A.valuation.Completion ≃ₐ[ℚ] A.valuation.Completion, (∀ c, s c = σ • c) →
          ∀ k : ↥K, s (k : A.valuation.Completion) = (k : A.valuation.Completion)) ∧
      (∀ n : ℕ, 0 < n → ¬ r ∣ n → ∀ k : (↥K)ˣ, ord (Additive.ofMul k) = 0 → ∃ k' : (↥K)ˣ, k' ^ n = k) ∧
      (∀ c : A.valuation.Completion,
        (∀ σ : ↥(A.decompositionSubgroup ℚ),
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ A.inertiaSubgroupIn ℚ →
          ∀ s : A.valuation.Completion ≃ₐ[ℚ] A.valuation.Completion, (∀ x, s x = σ • x) → s c = c) → c ∈ K) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Mumford_exists_periodField_completion.solution
