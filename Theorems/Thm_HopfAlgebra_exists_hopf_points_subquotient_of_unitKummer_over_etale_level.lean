import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_hopf_points_subquotient_of_unitKummer_over_etale_level

set_option autoImplicit false

theorem HopfAlgebra.exists_hopf_points_subquotient_of_unitKummer_over_etale_level
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
    ∃ (B : Type) (_ : CommRing B) (_ : IsDomain B) (_ : Algebra ℤ_[p] B) (_ : Module.Finite ℤ_[p] B)
      (_ : Module.Free ℤ_[p] B) (_ : Algebra.Etale ℤ_[p] B)
      (_ : Algebra B (AlgebraicClosure ℚ_[p])) (_ : IsScalarTower ℤ_[p] B (AlgebraicClosure ℚ_[p]))
      (HB : Type) (_ : CommRing HB) (_ : HopfAlgebra B HB) (_ : Module.Finite B HB) (_ : Module.Free B HB)
      (_ : Coalgebra.IsCocomm B HB)
      (Q' : AddSubmonoid (Additive (WithConv (HB →ₐ[B] AlgebraicClosure ℚ_[p]))))
      (ρ : ↥Q' →+ M),
      Function.Surjective ρ ∧
      (∀ f : ↥Q', ∃ g : ↥Q', (f : Additive (WithConv (HB →ₐ[B] AlgebraicClosure ℚ_[p]))) + g = 0) ∧
      (∀ σ : (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]),
        (∀ b : B, σ (algebraMap B (AlgebraicClosure ℚ_[p]) b) = algebraMap B (AlgebraicClosure ℚ_[p]) b) →
        ∀ (f : ↥Q') (g : WithConv (HB →ₐ[B] AlgebraicClosure ℚ_[p])),
          (∀ h : HB, g h = σ (Additive.toMul (f : Additive (WithConv (HB →ₐ[B] AlgebraicClosure ℚ_[p]))) h)) →
            ∃ hg : Additive.ofMul g ∈ Q', ρ ⟨Additive.ofMul g, hg⟩ = σ • ρ f) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_hopf_points_subquotient_of_unitKummer_over_etale_level.solution
