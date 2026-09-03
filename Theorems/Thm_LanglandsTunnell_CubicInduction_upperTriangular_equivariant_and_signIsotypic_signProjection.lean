import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_upperTriangular_equivariant_and_signIsotypic_signProjection

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.upperTriangular_equivariant_and_signIsotypic_signProjection
    (ν : Fin 3 → ℂ) (ε : Fin 3 → Fin 2) (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (heq : ∀ t : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, j < i → t i j = 0) → (∀ i : Fin 3, 0 < t i i) →
        ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, F (WhittakerBlock.archRealLift3 t * g) =
          (∏ a : Fin 3, ((t a a : ℝ) : ℂ) ^ (ν a + (![1, 0, -1] : Fin 3 → ℂ) a)) * F g) :
    (∀ t : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, j < i → t i j = 0) → (∀ i : Fin 3, 0 < t i i) →
        ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
          (fun g : AdelicGL 3 (𝓞 ℚ) ℚ => (1 / 8 : ℂ) * ∑ σ : Fin 3 → Fin 2,
        (-1 : ℂ) ^ (∑ a : Fin 3, (ε a : ℕ) * (σ a : ℕ)) *
          F (WhittakerBlock.archRealLift3 (fun a b => if a = b then (-1 : ℝ) ^ (σ a : ℕ) else 0) * g)) (WhittakerBlock.archRealLift3 t * g) =
            (∏ a : Fin 3, ((t a a : ℝ) : ℂ) ^ (ν a + (![1, 0, -1] : Fin 3 → ℂ) a)) *
              (fun g : AdelicGL 3 (𝓞 ℚ) ℚ => (1 / 8 : ℂ) * ∑ σ : Fin 3 → Fin 2,
        (-1 : ℂ) ^ (∑ a : Fin 3, (ε a : ℕ) * (σ a : ℕ)) *
          F (WhittakerBlock.archRealLift3 (fun a b => if a = b then (-1 : ℝ) ^ (σ a : ℕ) else 0) * g)) g) ∧
    (∀ τ : Fin 3 → Fin 2, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
        (fun g : AdelicGL 3 (𝓞 ℚ) ℚ => (1 / 8 : ℂ) * ∑ σ : Fin 3 → Fin 2,
        (-1 : ℂ) ^ (∑ a : Fin 3, (ε a : ℕ) * (σ a : ℕ)) *
          F (WhittakerBlock.archRealLift3 (fun a b => if a = b then (-1 : ℝ) ^ (σ a : ℕ) else 0) * g)) (WhittakerBlock.archRealLift3 (fun a b => if a = b then (-1 : ℝ) ^ (τ a : ℕ) else 0) * g) =
          (-1 : ℂ) ^ (∑ a : Fin 3, (ε a : ℕ) * (τ a : ℕ)) * (fun g : AdelicGL 3 (𝓞 ℚ) ℚ => (1 / 8 : ℂ) * ∑ σ : Fin 3 → Fin 2,
        (-1 : ℂ) ^ (∑ a : Fin 3, (ε a : ℕ) * (σ a : ℕ)) *
          F (WhittakerBlock.archRealLift3 (fun a b => if a = b then (-1 : ℝ) ^ (σ a : ℕ) else 0) * g)) g) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_upperTriangular_equivariant_and_signIsotypic_signProjection.solution
