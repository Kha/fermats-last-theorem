import Mathlib
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_projGenLinGroup_mk_unitsMap_eq_one_iff

set_option autoImplicit false

open scoped Quaternion MatrixGroups

theorem QuaternionAlgebra.projGenLinGroup_mk_unitsMap_eq_one_iff
    {a b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0)
    (L : Type) [Field L] [Algebra ℚ L]
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) L) (hι : Function.Injective ι)
    (ρ : (ℍ[ℚ, a, b])ˣ →* PGL(2, L))
    (hρ : ∀ x : (ℍ[ℚ, a, b])ˣ, ρ x = Matrix.ProjGenLinGroup.mk (Units.map (ι : ℍ[ℚ, a, b] →* Matrix (Fin 2) (Fin 2) L) x)) :
    ∀ x : (ℍ[ℚ, a, b])ˣ, ρ x = 1 ↔ ∃ c : ℚ, c ≠ 0 ∧ (x : ℍ[ℚ, a, b]) = algebraMap ℚ ℍ[ℚ, a, b] c := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_projGenLinGroup_mk_unitsMap_eq_one_iff.solution
