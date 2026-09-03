import Definitions.Def_AutomorphicForm_ArchWeightChar
import Mathlib
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_eq_archWeightCharReal_of_continuous

set_option autoImplicit false

open AutomorphicForm

theorem AutomorphicForm.exists_eq_archWeightCharReal_of_continuous
    (χ : rowIsometrySubgroup₀ ℝ →* ℂˣ)
    (hχ : Continuous fun k : rowIsometrySubgroup₀ ℝ => ((χ k : ℂˣ) : ℂ)) :
    ∃ m : ℤ, χ = archWeightCharℝ m := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_eq_archWeightCharReal_of_continuous.solution
