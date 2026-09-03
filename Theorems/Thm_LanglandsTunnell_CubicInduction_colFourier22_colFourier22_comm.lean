import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_GodementSection
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_colFourier22_colFourier22_comm

set_option autoImplicit false

p2m_open "MeasureTheory IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction~colFourier23_colFourier23_comm"

theorem LanglandsTunnell.CubicInduction.colFourier22_colFourier22_comm
    (v : HeightOneSpectrum (𝓞 ℚ)) (η : AddChar (v.adicCompletion ℚ) ℂ) (n : ℤ)
    (hηn : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp n → η x = 1)
    (hηn' : ∃ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (n + 1) ∧ η x ≠ 1)
    (ρ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ) → ℂ) (hρ : IsSchwartzBruhat ρ) :
    colFourier22 v η 0 (colFourier22 v η 1 ρ) = colFourier22 v η 1 (colFourier22 v η 0 ρ) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_colFourier22_colFourier22_comm.solution
