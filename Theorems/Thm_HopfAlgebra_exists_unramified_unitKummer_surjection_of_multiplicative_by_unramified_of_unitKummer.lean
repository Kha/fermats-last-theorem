import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_unramified_unitKummer_surjection_of_multiplicative_by_unramified_of_unitKummer

set_option autoImplicit false

open scoped BigOperators

theorem HopfAlgebra.exists_unramified_unitKummer_surjection_of_multiplicative_by_unramified_of_unitKummer
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (N : ℕ)
    (M : Type) [AddCommGroup M] [Finite M]
    [DistribMulAction (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) M]
    (hM : ∀ x : M, IsOpen (MulAction.stabilizer (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) x : Set (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])))
    (hpM : ∀ x : M, (p ^ N) • x = 0)
    (M₁ : AddSubgroup M) (hM₁ : ∀ (σ : (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])), ∀ y ∈ M₁, σ • y ∈ M₁)
    (n : (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) → ℕ)
    (hn : ∀ (τ : (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])) (ξ : AlgebraicClosure ℚ_[p]), ξ ^ p ^ N = 1 → τ ξ = ξ ^ n τ)
    (hmult : ∀ τ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p], ∀ y ∈ M₁, τ • y = n τ • y)
    (hquot : ∀ τ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p], ∀ x : M, τ • x - x ∈ M₁)
    (ζ : AlgebraicClosure ℚ_[p]) (hζ : IsPrimitiveRoot ζ (p ^ N))
    {t : ℕ} (u β : Fin t → AlgebraicClosure ℚ_[p])
    (hu : ∀ i, (padicIntegers p).valuation (u i) = 1)
    (huI : ∀ i, ∀ τ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p], τ (u i) = u i)
    (hβ : ∀ i, β i ^ p ^ N = u i)
    (φ : Fin t → (M →+ M)) (hφ₁ : ∀ i x, φ i x ∈ M₁) (hφ₀ : ∀ i, ∀ y ∈ M₁, φ i y = 0)
    (hdec : ∀ τ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p], (∀ ξ : AlgebraicClosure ℚ_[p], ξ ^ p ^ N = 1 → τ ξ = ξ) →
      ∀ k : Fin t → ℕ, (∀ i, τ (β i) = ζ ^ (k i) * β i) → ∀ x : M, τ • x - x = ∑ i, (k i) • φ i x) :
    ∃ (K : IntermediateField ℚ_[p] (AlgebraicClosure ℚ_[p])), FiniteDimensional ℚ_[p] ↥K ∧
      (padicIntegers p).inertiaSubgroupIn ℚ_[p] ≤ K.fixingSubgroup ∧
      (∀ σ ∈ K.fixingSubgroup, ∀ y ∈ M₁, σ • y = n σ • y) ∧
      (∀ σ ∈ K.fixingSubgroup, ∀ x : M, σ • x - x ∈ M₁) ∧
      ∃ (b a : ℕ) (r ρ : Fin b → Fin a → AlgebraicClosure ℚ_[p]) (κ : (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) → Fin b → Fin a → ℕ),
        (∀ m k, r m k ∈ K) ∧ (∀ m k, (padicIntegers p).valuation (r m k) = 1) ∧ (∀ m k, ρ m k ^ p ^ N = r m k) ∧
        (∀ σ ∈ K.fixingSubgroup, ∀ m k, σ (ρ m k) = ζ ^ κ σ m k * ρ m k) ∧
        ∃ π : (Fin b → ZMod (p ^ N)) × (Fin a → ZMod (p ^ N)) →+ M, Function.Surjective π ∧
          ∀ σ ∈ K.fixingSubgroup, ∀ (i : Fin b → ZMod (p ^ N)) (l : Fin a → ZMod (p ^ N)),
            π (fun m => n σ • i m + ∑ k, κ σ m k • l k, l) = σ • π (i, l) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_unramified_unitKummer_surjection_of_multiplicative_by_unramified_of_unitKummer.solution
