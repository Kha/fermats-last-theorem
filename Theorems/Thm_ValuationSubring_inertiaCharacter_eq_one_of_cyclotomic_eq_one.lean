import Definitions.Def_EllipticCurve_FrobeniusTrace
import Mathlib.Data.ZMod.Basic
import P2M.Util
import P2M.Sol.S_ValuationSubring_inertiaCharacter_eq_one_of_cyclotomic_eq_one

set_option autoImplicit false
open IsLocalRing Polynomial
theorem ValuationSubring.inertiaCharacter_eq_one_of_cyclotomic_eq_one
    {R : Type} [CommRing R] {q : ℕ} (hq : q.Prime)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    (ξ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → Rˣ)
    (hmul : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ τ ∈ P.inertiaSubgroupIn ℚ, ξ (σ * τ) = ξ σ * ξ τ)
    (hwild : ∀ σ ∈ P.inertiaSubgroupIn ℚ,
      (∀ z : AlgebraicClosure ℚ, z ≠ 0 → σ z * z⁻¹ - 1 ∈ P.nonunits) → ξ σ = 1)
    (hexp : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ξ σ ^ (q - 1) = 1)
    (hcont : ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L ∧
      ∀ σ ∈ P.inertiaSubgroupIn ℚ, (∀ x ∈ L, σ x = x) → ξ σ = 1)
    (cyc : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (ZMod q)ˣ)
    (hcyc : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (μ : AlgebraicClosure ℚ), μ ^ q = 1 →
      σ μ = μ ^ ((cyc σ : ZMod q).val))
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ : σ ∈ P.inertiaSubgroupIn ℚ) (hσc : cyc σ = 1) :
    ξ σ = 1 := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_inertiaCharacter_eq_one_of_cyclotomic_eq_one.solution
