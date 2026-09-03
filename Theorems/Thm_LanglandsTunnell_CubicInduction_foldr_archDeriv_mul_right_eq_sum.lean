import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_foldr_archDeriv_mul_right_eq_sum
attribute [-simp] LanglandsTunnell.CubicInduction.WhittakerBlock.coe_archDerivₗ_apply

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm

theorem LanglandsTunnell.CubicInduction.foldr_archDeriv_mul_right_eq_sum
    (w₀ : List (Fin 3 × Fin 3)) (k₀ : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ∃ (n : ℕ) (c : Fin n → ℂ) (ws : Fin n → List (Fin 3 × Fin 3)),
      (∀ i, (ws i).length = w₀.length) ∧
      ∀ u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, WhittakerBlock.IsArchSmooth3 u → ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
        List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) u w₀ (g * k₀) =
          ∑ i, c i * List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) (fun g => u (g * k₀)) (ws i) g := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_foldr_archDeriv_mul_right_eq_sum.solution
