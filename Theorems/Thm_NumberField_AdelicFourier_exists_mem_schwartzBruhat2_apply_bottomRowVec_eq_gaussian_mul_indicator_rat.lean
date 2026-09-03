import Definitions.Def_LanglandsTunnell_RS22GlobalIntegral
import Definitions.Def_LanglandsTunnell_DeltaLift
import P2M.Util
import P2M.Sol.S_NumberField_AdelicFourier_exists_mem_schwartzBruhat2_apply_bottomRowVec_eq_gaussian_mul_indicator_rat

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicFourier IsDedekindDomain AutomorphicForm LanglandsTunnell
open scoped Classical

theorem NumberField.AdelicFourier.exists_mem_schwartzBruhat2_apply_bottomRowVec_eq_gaussian_mul_indicator_rat
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (m : HeightOneSpectrum (𝓞 ℚ) → ℕ) :
    ∃ Φ : (Fin 2 → AdeleRing (𝓞 ℚ) ℚ) → ℂ, Φ ∈ schwartzBruhat2 ℚ ∧
      ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
        Φ (bottomRowVec ℚ g 1) =
          (Real.exp (-(Real.pi *
              (((ratArchGL2 g : Matrix (Fin 2) (Fin 2) ℝ) 1 0) ^ 2 + ((ratArchGL2 g : Matrix (Fin 2) (Fin 2) ℝ) 1 1) ^ 2))) : ℂ) *
          (if (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → ∀ j : Fin 2,
                Valued.v ((((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 j).2) p) ≤ 1) ∧
              (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∈ S →
                Valued.v ((((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 0).2) p) ≤ WithZero.exp (-(m p : ℤ)) ∧
                Valued.v ((((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 1).2) p - 1) ≤ WithZero.exp (-(m p : ℤ)))
            then (1 : ℂ) else 0) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdelicFourier_exists_mem_schwartzBruhat2_apply_bottomRowVec_eq_gaussian_mul_indicator_rat.solution
