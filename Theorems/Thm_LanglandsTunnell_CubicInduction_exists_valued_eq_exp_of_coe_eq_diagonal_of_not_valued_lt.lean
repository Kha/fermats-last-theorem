import Definitions.Def_LanglandsTunnell_CubicInduction_HeckeDatum
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_exists_valued_eq_exp_of_coe_eq_diagonal_of_not_valued_lt

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem LanglandsTunnell.CubicInduction.exists_valued_eq_exp_of_coe_eq_diagonal_of_not_valued_lt
    (v : HeightOneSpectrum (𝓞 ℚ)) (t : LocalGL3 v) (d : Fin 3 → v.adicCompletion ℚ)
    (ht : (t : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) = Matrix.diagonal d)
    (hd : ¬ (Valued.v (d 1) < Valued.v (d 0) ∨ Valued.v (d 2) < Valued.v (d 1))) :
    ∃ (k₁ k₂ : ℕ) (c : ℤ), Valued.v (d 0) = WithZero.exp (-((k₁ : ℤ) + c)) ∧
      Valued.v (d 1) = WithZero.exp (-((k₂ : ℤ) + c)) ∧ Valued.v (d 2) = WithZero.exp (-c) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_valued_eq_exp_of_coe_eq_diagonal_of_not_valued_lt.solution
