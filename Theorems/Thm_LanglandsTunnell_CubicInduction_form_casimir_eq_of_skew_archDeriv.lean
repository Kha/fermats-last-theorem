import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_form_casimir_eq_of_skew_archDeriv

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell.CubicInduction

theorem
LanglandsTunnell.CubicInduction.form_casimir_eq_of_skew_archDeriv
    (M : Submodule ℂ (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))
    (h5 : ∀ w ∈ M, ∀ i j : Fin 3, WhittakerBlock.archDeriv i j w ∈ M)
    (B : (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) → (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) → ℂ)
    (hherm : ∀ w ∈ M, ∀ w' ∈ M, B w' w = (starRingEnd ℂ) (B w w'))
    (hlin : ∀ (z : ℂ), ∀ w₁ ∈ M, ∀ w₂ ∈ M, ∀ w' ∈ M, B (z • w₁ + w₂) w' = z * B w₁ w' + B w₂ w')
    (hskew : ∀ w ∈ M, ∀ w' ∈ M, ∀ i j : Fin 3,
      B (WhittakerBlock.archDeriv i j w) w' = - B w (WhittakerBlock.archDeriv i j w'))
    (w : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hw : w ∈ M) (w' : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hw' : w' ∈ M) :
    B (WhittakerBlock.casimir1 w) w' = - B w (WhittakerBlock.casimir1 w') ∧
    B (WhittakerBlock.casimir2 w) w' = B w (WhittakerBlock.casimir2 w') ∧
    B (WhittakerBlock.casimir3 w) w' =
      - B w (fun g => ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
          WhittakerBlock.archDeriv i j (WhittakerBlock.archDeriv k i (WhittakerBlock.archDeriv j k w')) g) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_form_casimir_eq_of_skew_archDeriv.solution
