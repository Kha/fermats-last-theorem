import Definitions.Def_EllipticCurve_FrobeniusTrace
import P2M.Util
import P2M.Sol.S_TWLoc_frobenius_conj_mul_pow_inv_wild

set_option autoImplicit false
theorem TWLoc.frobenius_conj_mul_pow_inv_wild {q : ℕ} (P : ValuationSubring (AlgebraicClosure ℚ))
    {φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hφ : P.IsFrobeniusAt φ q)
    {τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hτ : τ ∈ P.inertiaSubgroupIn ℚ) :
    φ * τ * φ⁻¹ * (τ ^ q)⁻¹ ∈ P.inertiaSubgroupIn ℚ ∧
      ∀ z : AlgebraicClosure ℚ, z ≠ 0 → (φ * τ * φ⁻¹ * (τ ^ q)⁻¹) z * z⁻¹ - 1 ∈ P.nonunits := by p2m_exact_reverting @_root_.P2MW.S_TWLoc_frobenius_conj_mul_pow_inv_wild.solution
