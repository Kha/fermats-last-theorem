import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
import P2M.Util
import P2M.Sol.S_PadicAlgCl_exists_root_one_add_prime_forall_inertia_residual_trivial

set_option autoImplicit false
theorem PadicAlgCl.exists_root_one_add_prime_forall_inertia_residual_trivial
    {B : Type} [CommRing B] [IsLocalRing B] (p : ℕ) [Fact p.Prime]
    (hpB : (p : B) ∈ IsLocalRing.maximalIdeal B)
    (x z : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) → Bˣ) (y : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) → B)
    (hzI : ∀ τ : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), τ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] → z τ = 1)
    (hcyc : ∀ (g : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)) (n a : ℕ), (∀ μ : PadicAlgCl p, μ ^ p ^ n = 1 → g μ = μ ^ a) →
      (x g : B) * (z g : B) - (a : B) ∈ Ideal.span {((p ^ n : ℕ) : B)})
    (η : B) (hη : IsUnit η) (ζ : PadicAlgCl p) (hζ : IsPrimitiveRoot ζ p)
    (hall : ∀ Λ : IsLocalRing.ResidueField B →+ ZMod p,
      ∃ (a : ℚ_[p]ˣ) (α : (PadicAlgCl p)ˣ),
        algebraMap ℚ_[p] (PadicAlgCl p) (a : ℚ_[p]) = (α : PadicAlgCl p) ^ p ∧
        (∀ g : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), g (α : PadicAlgCl p) =
          ζ ^ (Λ (IsLocalRing.residue B (η * (y g * (((z g)⁻¹ : Bˣ) : B))))).val * (α : PadicAlgCl p)) ∧
        (p : ℤ) ∣ Padic.valuation (a : ℚ_[p]))
    (hU : ∀ c : ℚ_[p], c ≠ 0 → (p : ℤ) ∣ Padic.valuation c →
      ∃ (r : ℕ) (w : ℚ_[p]), c = (1 + (p : ℚ_[p])) ^ r * w ^ p) :
    ∃ β : PadicAlgCl p, β ^ p = 1 + (p : PadicAlgCl p) ∧
      ∀ τ : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), τ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] →
        (∀ ξ : PadicAlgCl p, ξ ^ p = 1 → τ ξ = ξ) → τ β = β →
          (x τ : B) - 1 ∈ IsLocalRing.maximalIdeal B ∧ y τ ∈ IsLocalRing.maximalIdeal B ∧
            (z τ : B) = 1 := by p2m_exact_reverting @_root_.P2MW.S_PadicAlgCl_exists_root_one_add_prime_forall_inertia_residual_trivial.solution
