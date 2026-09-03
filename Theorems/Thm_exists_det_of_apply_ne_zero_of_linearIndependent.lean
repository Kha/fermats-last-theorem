import Mathlib
import P2M.Util
import P2M.Sol.S_exists_det_of_apply_ne_zero_of_linearIndependent

set_option autoImplicit false

theorem exists_det_of_apply_ne_zero_of_linearIndependent
    {𝕜 : Type*} [Field 𝕜] {X : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → X → 𝕜) (hf : LinearIndependent 𝕜 f) :
    ∃ x : ι → X, (Matrix.of fun i j : ι => f j (x i)).det ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_exists_det_of_apply_ne_zero_of_linearIndependent.solution
