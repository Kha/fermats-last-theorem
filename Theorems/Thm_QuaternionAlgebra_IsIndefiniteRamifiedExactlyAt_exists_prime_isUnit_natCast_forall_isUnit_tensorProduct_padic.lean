import Mathlib
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_IsIndefiniteRamifiedExactlyAt_exists_prime_isUnit_natCast_forall_isUnit_tensorProduct_padic

set_option autoImplicit false

open scoped Quaternion TensorProduct

theorem QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt.exists_prime_isUnit_natCast_forall_isUnit_tensorProduct_padic
    {a b : ℚ} {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hne : q ≠ q')
    (hB : QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt a b q q')
    (R : Type*) [CommRing R] [IsLocalRing R] :
    ∃ (ℓ : ℕ) (_ : Fact ℓ.Prime), (ℓ = q ∨ ℓ = q') ∧ IsUnit (ℓ : R) ∧
      ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] ℚ_[ℓ], x ≠ 0 → IsUnit x := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_IsIndefiniteRamifiedExactlyAt_exists_prime_isUnit_natCast_forall_isUnit_tensorProduct_padic.solution
