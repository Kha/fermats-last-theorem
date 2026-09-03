import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_GodementSection
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_colFourier23_colFourier23_comm

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.colFourier23_colFourier23_comm
    (v : HeightOneSpectrum (𝓞 ℚ)) (η : AddChar (v.adicCompletion ℚ) ℂ) (n : ℤ)
    (hηn : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp n → η x = 1)
    (hηn' : ∃ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (n + 1) ∧ η x ≠ 1)
    (a b : Fin 3) (hab : a ≠ b)
    (ρ : Matrix (Fin 2) (Fin 3) (v.adicCompletion ℚ) → ℂ) (hρ : IsSchwartzBruhat ρ) :
    colFourier23 v η a (colFourier23 v η b ρ) = colFourier23 v η b (colFourier23 v η a ρ) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_colFourier23_colFourier23_comm.solution
