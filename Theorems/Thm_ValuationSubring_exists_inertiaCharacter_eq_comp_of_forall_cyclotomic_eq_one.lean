import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_Deformations_TameDescent
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_inertiaCharacter_eq_comp_of_forall_cyclotomic_eq_one

set_option autoImplicit false

open IsLocalRing
theorem ValuationSubring.exists_inertiaCharacter_eq_comp_of_forall_cyclotomic_eq_one
    {R : Type} [CommRing R] [IsLocalRing R] {q : ℕ} (hq : q.Prime) {p : ℕ} (hp : p.Prime)
    (hpR : (p : R) ∈ IsLocalRing.maximalIdeal R) {k : ℕ} (hk : ¬ p ^ (k + 1) ∣ q - 1)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    (ξ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → Rˣ)
    (hmul : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ τ ∈ P.inertiaSubgroupIn ℚ, ξ (σ * τ) = ξ σ * ξ τ)
    (hone : ∀ σ ∈ P.inertiaSubgroupIn ℚ, (ξ σ : R) - 1 ∈ IsLocalRing.maximalIdeal R)
    (cyc : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (ZMod q)ˣ)
    (hcyc : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (μ : AlgebraicClosure ℚ), μ ^ q = 1 →
      σ μ = μ ^ ((cyc σ : ZMod q).val))
    (hker : ∀ σ ∈ P.inertiaSubgroupIn ℚ, cyc σ = 1 → ξ σ = 1)
    (πΔ : (ZMod q)ˣ →* Multiplicative (ZMod (p ^ k))) (hπΔ : Function.Surjective πΔ) :
    ∃ χ : Multiplicative (ZMod (p ^ k)) →* Rˣ, ∀ σ ∈ P.inertiaSubgroupIn ℚ, ξ σ = χ (πΔ (cyc σ)) := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_inertiaCharacter_eq_comp_of_forall_cyclotomic_eq_one.solution
