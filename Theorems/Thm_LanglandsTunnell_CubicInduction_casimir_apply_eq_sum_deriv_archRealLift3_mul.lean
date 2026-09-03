import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_casimir_apply_eq_sum_deriv_archRealLift3_mul
attribute [-simp] LanglandsTunnell.CubicInduction.WhittakerBlock.coe_archDerivₗ_apply

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.casimir_apply_eq_sum_deriv_archRealLift3_mul
    (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hsa : WhittakerBlock.IsArchSmooth3 φ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    WhittakerBlock.casimir1 φ g
      = ∑ i : Fin 3, deriv (fun s : ℝ => φ (WhittakerBlock.archRealLift3 (fun a b => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = i then s else 0) * g)) 0 ∧
    WhittakerBlock.casimir2 φ g
      = ∑ i : Fin 3, ∑ j : Fin 3,
          deriv (fun t : ℝ => deriv (fun s : ℝ =>
            φ (WhittakerBlock.archRealLift3 (fun a b => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0) * (WhittakerBlock.archRealLift3 (fun a b => (if a = b then (1 : ℝ) else 0) + if a = j ∧ b = i then t else 0) * g))) 0) 0 ∧
    WhittakerBlock.casimir3 φ g
      = ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
          deriv (fun u : ℝ => deriv (fun t : ℝ => deriv (fun s : ℝ =>
            φ (WhittakerBlock.archRealLift3 (fun a b => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0) * (WhittakerBlock.archRealLift3 (fun a b => (if a = b then (1 : ℝ) else 0) + if a = j ∧ b = k then t else 0) * (WhittakerBlock.archRealLift3 (fun a b => (if a = b then (1 : ℝ) else 0) + if a = k ∧ b = i then u else 0) * g)))) 0) 0) 0 := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_casimir_apply_eq_sum_deriv_archRealLift3_mul.solution
