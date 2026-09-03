import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_isArchSmooth3_deriv_archRealLift3_mul_and_linear_and_bracket

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.isArchSmooth3_deriv_archRealLift3_mul_and_linear_and_bracket
    (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hsa : WhittakerBlock.IsArchSmooth3 φ) :
    (∀ X : Fin 3 → Fin 3 → ℝ,
      WhittakerBlock.IsArchSmooth3 (fun g => deriv (fun s : ℝ => φ (WhittakerBlock.archRealLift3 (fun a b => (if a = b then (1 : ℝ) else 0) + s * X a b) * g)) 0)) ∧
    (∀ (X Y : Fin 3 → Fin 3 → ℝ) (α β : ℝ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      deriv (fun s : ℝ => φ (WhittakerBlock.archRealLift3 (fun a b => (if a = b then (1 : ℝ) else 0) + s * (fun a' b' => α * X a' b' + β * Y a' b') a b) * g)) 0
        = (α : ℂ) * deriv (fun s : ℝ => φ (WhittakerBlock.archRealLift3 (fun a b => (if a = b then (1 : ℝ) else 0) + s * X a b) * g)) 0
          + (β : ℂ) * deriv (fun s : ℝ => φ (WhittakerBlock.archRealLift3 (fun a b => (if a = b then (1 : ℝ) else 0) + s * Y a b) * g)) 0) ∧
    (∀ (X Y : Fin 3 → Fin 3 → ℝ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      deriv (fun t : ℝ => deriv (fun s : ℝ => φ (WhittakerBlock.archRealLift3 (fun a b => (if a = b then (1 : ℝ) else 0) + s * X a b) * (WhittakerBlock.archRealLift3 (fun a b => (if a = b then (1 : ℝ) else 0) + t * Y a b) * g))) 0) 0
        - deriv (fun t : ℝ => deriv (fun s : ℝ => φ (WhittakerBlock.archRealLift3 (fun a b => (if a = b then (1 : ℝ) else 0) + s * Y a b) * (WhittakerBlock.archRealLift3 (fun a b => (if a = b then (1 : ℝ) else 0) + t * X a b) * g))) 0) 0
        = deriv (fun s : ℝ => φ (WhittakerBlock.archRealLift3 (fun a b => (if a = b then (1 : ℝ) else 0) + s * (fun a' b' => (Matrix.of X * Matrix.of Y - Matrix.of Y * Matrix.of X) a' b') a b) * g)) 0) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_isArchSmooth3_deriv_archRealLift3_mul_and_linear_and_bracket.solution
