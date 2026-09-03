import Mathlib
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_TateLocal_exists_finset_forall_eq_sum_mul_prod_indicator_ball_of_isLocallyConstant_of_hasCompactSupport

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory LanglandsTunnell.TateLocal

theorem LanglandsTunnell.TateLocal.exists_finset_forall_eq_sum_mul_prod_indicator_ball_of_isLocallyConstant_of_hasCompactSupport
    (p : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ)
    (Φ : (Fin n → p.adicCompletion ℚ) → ℂ) (hΦ : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ) :
    ∃ (N : ℤ) (S : Finset (Fin n → p.adicCompletion ℚ)),
      (∀ c ∈ S, ∀ c' ∈ S, c ≠ c' →
        Disjoint {v : Fin n → p.adicCompletion ℚ | ∀ j, Valued.v (v j - c j) ≤ WithZero.exp N}
                 {v : Fin n → p.adicCompletion ℚ | ∀ j, Valued.v (v j - c' j) ≤ WithZero.exp N}) ∧
      ∀ v : Fin n → p.adicCompletion ℚ,
        Φ v = ∑ c ∈ S, Φ c * ∏ j : Fin n,
          ({x : p.adicCompletion ℚ | Valued.v (x - c j) ≤ WithZero.exp N}.indicator (fun _ => (1 : ℂ)) (v j)) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_TateLocal_exists_finset_forall_eq_sum_mul_prod_indicator_ball_of_isLocallyConstant_of_hasCompactSupport.solution
