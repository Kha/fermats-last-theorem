import Mathlib
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_eq_archWeightCharReal_of_hasArchCharacterAt_of_continuous

set_option autoImplicit false

open NumberField AutomorphicForm AutomorphicForm.WindowedSiegel NumberField.InfinitePlace
  NumberField.InfinitePlace.Completion

theorem AutomorphicForm.exists_eq_archWeightCharReal_of_hasArchCharacterAt_of_continuous
    (F : Type) [Field F] [NumberField F] (w : InfinitePlace F) (hw : w.IsReal)
    (χ : rowIsometrySubgroup₀ ℝ →* ℂˣ) (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : Continuous φ)
    (hφ0 : ∃ g : AdelicGL2 (𝓞 F) F, φ g ≠ 0)
    (hχ : HasArchCharacterAt₀ F w
      (χ.comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw)))
      φ) :
    ∃ n : ℤ, χ = archWeightCharℝ n := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_eq_archWeightCharReal_of_hasArchCharacterAt_of_continuous.solution
