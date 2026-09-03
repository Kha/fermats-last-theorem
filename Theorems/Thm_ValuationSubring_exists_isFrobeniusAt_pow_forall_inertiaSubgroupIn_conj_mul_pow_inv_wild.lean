import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_FrobeniusTrace
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_isFrobeniusAt_pow_forall_inertiaSubgroupIn_conj_mul_pow_inv_wild
attribute [-simp] WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply

set_option autoImplicit false

theorem ValuationSubring.exists_isFrobeniusAt_pow_forall_inertiaSubgroupIn_conj_mul_pow_inv_wild
    (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥K] :
    ∃ (d : ℕ) (φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), 0 < d ∧ (∀ z ∈ K, φ z = z) ∧
      A.IsFrobeniusAt φ (p ^ d) ∧
      ∀ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, τ ∈ A.inertiaSubgroupIn ℚ →
        φ * τ * φ⁻¹ * (τ ^ (p ^ d))⁻¹ ∈ A.inertiaSubgroupIn ℚ ∧
        (∀ z : AlgebraicClosure ℚ, z ≠ 0 →
          (φ * τ * φ⁻¹ * (τ ^ (p ^ d))⁻¹) z * z⁻¹ - 1 ∈ A.nonunits) ∧
        ∀ (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥F] [Normal ℚ ↥F],
          ∃ a : ℕ, ∀ x ∈ F, ((φ * τ * φ⁻¹ * (τ ^ (p ^ d))⁻¹) ^ (p ^ a)) x = x := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_isFrobeniusAt_pow_forall_inertiaSubgroupIn_conj_mul_pow_inv_wild.solution
