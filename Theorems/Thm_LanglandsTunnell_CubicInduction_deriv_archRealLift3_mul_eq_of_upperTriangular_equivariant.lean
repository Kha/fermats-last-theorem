import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_deriv_archRealLift3_mul_eq_of_upperTriangular_equivariant

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.deriv_archRealLift3_mul_eq_of_upperTriangular_equivariant
    (ν : Fin 3 → ℂ) (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hB : ∀ e : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, j < i → e i j = 0) → (∀ i : Fin 3, 0 < e i i) →
      ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
        F (WhittakerBlock.archRealLift3 e * g) =
          (∏ a : Fin 3, ((e a a : ℝ) : ℂ) ^ (ν a + (![1, 0, -1] : Fin 3 → ℂ) a)) * F g) :
    (∀ i j : Fin 3, i < j → ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      deriv (fun s : ℝ => F (WhittakerBlock.archRealLift3 (fun a b => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0) * g)) 0 = 0) ∧
    (∀ (c : Fin 3) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      deriv (fun s : ℝ => F (WhittakerBlock.archRealLift3 (fun a b => (if a = b then (1 : ℝ) else 0) + if a = c ∧ b = c then s else 0) * g)) 0 =
        (ν c + (![1, 0, -1] : Fin 3 → ℂ) c) * F g) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_deriv_archRealLift3_mul_eq_of_upperTriangular_equivariant.solution
