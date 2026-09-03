import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_LanglandsTunnell_CubicInduction_SlabL2Cusp
import Definitions.Def_LanglandsTunnell_CubicInduction_AdelicEpstein
import Definitions.Def_LanglandsTunnell_CubicInduction_Growth
import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_AdelicHaar
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_exists_measurable_bounded_compactArch_integral_pos_on_thirdRow_window

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField AutomorphicForm MeasureTheory NumberField.StandardAddChar
open LanglandsTunnell.CubicInduction LanglandsTunnell.CubicInduction.SlabL2
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.adeleBorel

theorem LanglandsTunnell.CubicInduction.exists_measurable_bounded_compactArch_integral_pos_on_thirdRow_window
    (B : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) (hB : IsCompact B) (b₀ : ℝ) (hb₀ : 1 < b₀) :
    ∃ (Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ) (M R₀ : ℝ) (N : ℕ) (φ₀ : ℝ),
      0 ≤ R₀ ∧ 0 < N ∧ 0 < φ₀ ∧ Measurable Φ ∧ (∀ x, ‖Φ x‖ ≤ M) ∧
      (∀ x, Φ x ≠ 0 → ∀ i, ‖(x i).1 Rat.infinitePlace‖ ≤ R₀) ∧
      (∀ x, Φ x ≠ 0 → ∀ (i : Fin 3) (w : HeightOneSpectrum (𝓞 ℚ)),
        ((N : IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ) * (x i).2) w ∈ w.adicCompletionIntegers ℚ) ∧
      (∀ k ∈ B, ∀ a : Fin 3 → ℝ, (∀ i, 0 < a i) → b₀⁻¹ ≤ a 2 → a 2 ≤ b₀ →
        φ₀ ≤ ‖Φ fun j : Fin 3 => ((WhittakerBlock.archRealLift3 (fun i j => if i = j then a i else 0) * k :
                      AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j‖) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_measurable_bounded_compactArch_integral_pos_on_thirdRow_window.solution
