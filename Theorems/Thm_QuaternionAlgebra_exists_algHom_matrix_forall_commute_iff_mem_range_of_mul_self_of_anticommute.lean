import Mathlib
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_exists_algHom_matrix_forall_commute_iff_mem_range_of_mul_self_of_anticommute

set_option autoImplicit false

open scoped Quaternion

theorem QuaternionAlgebra.exists_algHom_matrix_forall_commute_iff_mem_range_of_mul_self_of_anticommute
    {c d : ℚ} (t s c' : ℚ) (ht : t ≠ 0) (hs : s ≠ 0) (hc' : c' ≠ 0)
    (y z : ℍ[ℚ, c, d]) (hy : y * y = algebraMap ℚ ℍ[ℚ, c, d] t) (hz : z * z = algebraMap ℚ ℍ[ℚ, c, d] c')
    (hyz : y * z = -(z * y))
    (hspan : ∀ u : ℍ[ℚ, c, d], ∃ α β γ δ : ℚ, u = α • 1 + β • y + γ • z + δ • (y * z)) :
    ∃ τ : ℍ[ℚ, t, s * c'] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d],
      Function.Injective τ ∧
      τ ⟨0, 1, 0, 0⟩ = !![y, 0; 0, y] ∧ τ ⟨0, 0, 1, 0⟩ = !![0, s • z; z, 0] ∧
      ∀ Y : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d],
        (Y * !![y, 0; 0, -y] = !![y, 0; 0, -y] * Y ∧
            Y * !![0, algebraMap ℚ ℍ[ℚ, c, d] s; 1, 0] = !![0, algebraMap ℚ ℍ[ℚ, c, d] s; 1, 0] * Y) ↔
          Y ∈ Set.range τ := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_exists_algHom_matrix_forall_commute_iff_mem_range_of_mul_self_of_anticommute.solution
