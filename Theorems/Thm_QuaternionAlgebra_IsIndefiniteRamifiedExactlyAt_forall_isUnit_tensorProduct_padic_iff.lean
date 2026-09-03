import Mathlib
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_IsIndefiniteRamifiedExactlyAt_forall_isUnit_tensorProduct_padic_iff

set_option autoImplicit false

open scoped Quaternion TensorProduct

theorem QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt.forall_isUnit_tensorProduct_padic_iff
    {a b : ℚ} {q q' : ℕ} (hB : QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt a b q q')
    (ℓ : ℕ) [Fact ℓ.Prime] :
    (∀ x : ℍ[ℚ, a, b] ⊗[ℚ] ℚ_[ℓ], x ≠ 0 → IsUnit x) ↔ (ℓ ∣ q ∨ ℓ ∣ q') := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_IsIndefiniteRamifiedExactlyAt_forall_isUnit_tensorProduct_padic_iff.solution
