import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_GodementSection
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_isSchwartzBruhat_colFourier23

set_option autoImplicit false

p2m_open "MeasureTheory IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.TateLocal~isSchwartzBruhat_tateFourier LanglandsTunnell.CubicInduction"

theorem LanglandsTunnell.CubicInduction.isSchwartzBruhat_colFourier23
    (v : HeightOneSpectrum (𝓞 ℚ)) (η : AddChar (v.adicCompletion ℚ) ℂ) (n : ℤ)
    (hηn : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp n → η x = 1)
    (hηn' : ∃ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (n + 1) ∧ η x ≠ 1)
    (j : Fin 3) (Φ : Matrix (Fin 2) (Fin 3) (v.adicCompletion ℚ) → ℂ) (hΦ : IsSchwartzBruhat Φ) :
    IsSchwartzBruhat (colFourier23 v η j Φ) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_isSchwartzBruhat_colFourier23.solution
