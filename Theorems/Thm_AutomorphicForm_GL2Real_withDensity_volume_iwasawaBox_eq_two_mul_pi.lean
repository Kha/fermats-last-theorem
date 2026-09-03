import Mathlib
import Definitions.Def_AutomorphicForm_ArchWeightChar
import P2M.Util
import P2M.Sol.S_AutomorphicForm_GL2Real_withDensity_volume_iwasawaBox_eq_two_mul_pi

set_option autoImplicit false

open MeasureTheory AutomorphicForm

theorem AutomorphicForm.GL2Real.withDensity_volume_iwasawaBox_eq_two_mul_pi :
    ((volume : Measure (Fin 2 → Fin 2 → ℝ)).withDensity
        fun q => (ENNReal.ofReal ((Matrix.of q).det ^ 2))⁻¹)
      {q | ∃ b₁ ∈ Set.Icc (1 : ℝ) (Real.exp 1), ∃ b₂ ∈ Set.Icc (1 : ℝ) (Real.exp 1),
          ∃ x ∈ Set.Icc (0 : ℝ) 1, ∃ k : rowIsometrySubgroup₀ ℝ,
          Matrix.of q = !![b₁, b₁ * x; 0, b₂] * ((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)} =
      ENNReal.ofReal (2 * Real.pi) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_GL2Real_withDensity_volume_iwasawaBox_eq_two_mul_pi.solution
