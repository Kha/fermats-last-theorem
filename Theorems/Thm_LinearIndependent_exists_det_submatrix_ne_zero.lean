import Mathlib
import P2M.Util
import P2M.Sol.S_LinearIndependent_exists_det_submatrix_ne_zero

theorem LinearIndependent.exists_det_submatrix_ne_zero
    {k : Type*} [Field k] {ι : Type*} {n : ℕ}
    (f : Fin n → ι → k) (hf : LinearIndependent k f) :
    ∃ s : Fin n → ι, Function.Injective s ∧ (Matrix.of fun l j => f j (s l)).det ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_LinearIndependent_exists_det_submatrix_ne_zero.solution
