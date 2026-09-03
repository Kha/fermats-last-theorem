import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_exists_algHom_matrix_injective_apply_eq_of_isDefiniteRamifiedExactlyAt_of_forall_isUnit_of_pos

set_option autoImplicit false

open scoped Quaternion TensorProduct
open IsDedekindDomain NumberField

theorem QuaternionAlgebra.exists_algHom_matrix_injective_apply_eq_of_isDefiniteRamifiedExactlyAt_of_forall_isUnit_of_pos
    {a b c d : ℚ} (q : ℕ) [Fact q.Prime]
    (hH : QuaternionAlgebra.IsDefiniteRamifiedExactlyAt c d q)
    (hBq : ∀ v : HeightOneSpectrum (𝓞 ℚ), (q : 𝓞 ℚ) ∈ v.asIdeal →
      ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, x ≠ 0 → IsUnit x)
    (hab : 0 < a ∨ 0 < b) :
    ∃ (t s : ℚ) (x w : ℍ[ℚ, a, b]) (y : ℍ[ℚ, c, d]) (ρ : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]),
      t < 0 ∧ 0 < s ∧
      x * x = algebraMap ℚ ℍ[ℚ, a, b] t ∧ w * w = algebraMap ℚ ℍ[ℚ, a, b] s ∧ x * w = -(w * x) ∧
      (∀ u : ℍ[ℚ, a, b], ∃ α β γ δ : ℚ, u = α • 1 + β • x + γ • w + δ • (x * w)) ∧
      y * y = algebraMap ℚ ℍ[ℚ, c, d] t ∧
      Function.Injective ρ ∧
      ρ x = !![y, 0; 0, -y] ∧ ρ w = !![0, algebraMap ℚ ℍ[ℚ, c, d] s; 1, 0] := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_exists_algHom_matrix_injective_apply_eq_of_isDefiniteRamifiedExactlyAt_of_forall_isUnit_of_pos.solution
