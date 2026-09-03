import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_FrobeniusTrace
import P2M.Util
import P2M.Sol.S_ValuationSubring_IsFrobeniusAt_conj_mul_pow_inv_mem_inertiaSubgroupIn_and_wild

set_option autoImplicit false

theorem ValuationSubring.IsFrobeniusAt.conj_mul_pow_inv_mem_inertiaSubgroupIn_and_wild
    {K L : Type*} [Field K] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
    {q : ℕ} {P : ValuationSubring L}
    {φ : L ≃ₐ[K] L} (hφ : P.IsFrobeniusAt φ q) {τ : L ≃ₐ[K] L} (hτ : τ ∈ P.inertiaSubgroupIn K) :
    φ * τ * φ⁻¹ * (τ ^ q)⁻¹ ∈ P.inertiaSubgroupIn K ∧
      ∀ z : L, z ≠ 0 → (φ * τ * φ⁻¹ * (τ ^ q)⁻¹) z * z⁻¹ - 1 ∈ P.nonunits := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_IsFrobeniusAt_conj_mul_pow_inv_mem_inertiaSubgroupIn_and_wild.solution
