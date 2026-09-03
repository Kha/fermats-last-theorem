import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_GodementSection
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_matFourier23_comp_mul_transvection_eq

set_option autoImplicit false

p2m_open "MeasureTheory IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction~isSchwartzBruhat_colFourier23~colFourier23_colFourier23_comm"

theorem LanglandsTunnell.CubicInduction.matFourier23_comp_mul_transvection_eq
    (v : HeightOneSpectrum (𝓞 ℚ)) (η : AddChar (v.adicCompletion ℚ) ℂ) (n : ℤ)
    (hηn : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp n → η x = 1)
    (hηn' : ∃ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (n + 1) ∧ η x ≠ 1)
    (ρ : Matrix (Fin 2) (Fin 3) (v.adicCompletion ℚ) → ℂ) (hρ : IsSchwartzBruhat ρ)
    (i j : Fin 3) (hij : i ≠ j) (c : v.adicCompletion ℚ) (X : Matrix (Fin 2) (Fin 3) (v.adicCompletion ℚ)) :
    matFourier23 v η (fun Y => ρ (Y * Matrix.transvection i j c)) X =
      matFourier23 v η ρ (X * Matrix.transvection j i (-c)) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_matFourier23_comp_mul_transvection_eq.solution
