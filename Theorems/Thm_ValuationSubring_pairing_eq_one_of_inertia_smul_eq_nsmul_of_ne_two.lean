import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ValuationSubring_pairing_eq_one_of_inertia_smul_eq_nsmul_of_ne_two
set_option autoImplicit false

theorem ValuationSubring.pairing_eq_one_of_inertia_smul_eq_nsmul_of_ne_two
    {M : Type*} [AddCommGroup M] [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) M]
    (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (k : ℕ) (n : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → ℕ)
    (hn : ∀ σ, ∀ ζ : AlgebraicClosure ℚ, ζ ^ (q ^ k) = 1 → σ ζ = ζ ^ n σ)
    (B : M → M → AlgebraicClosure ℚ)
    (W : Set M)
    (hWμ : ∀ x ∈ W, ∀ σ ∈ A.inertiaSubgroupIn ℚ, σ • x = n σ • x)
    (hWnsmul : ∀ x ∈ W, ∀ m : ℕ, m • x ∈ W)
    (hBval : ∀ x ∈ W, ∀ y ∈ W, B x y ^ (q ^ k) = 1)
    (hBl : ∀ x ∈ W, ∀ y ∈ W, ∀ m : ℕ, B (m • x) y = B x y ^ m)
    (hBr : ∀ x ∈ W, ∀ y ∈ W, ∀ m : ℕ, B x (m • y) = B x y ^ m)
    (hBgal : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ x ∈ W, ∀ y ∈ W, B (σ • x) (σ • y) = σ (B x y)) :
    ∀ x ∈ W, ∀ y ∈ W, B x y = 1 := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_pairing_eq_one_of_inertia_smul_eq_nsmul_of_ne_two.solution
