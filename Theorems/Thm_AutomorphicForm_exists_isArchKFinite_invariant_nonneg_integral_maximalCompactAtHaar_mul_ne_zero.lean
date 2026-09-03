import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_BorelSubgroup
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_isArchKFinite_invariant_nonneg_integral_maximalCompactAtHaar_mul_ne_zero

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel AutomorphicForm AutomorphicForm.WindowedSiegel IsDedekindDomain

theorem AutomorphicForm.exists_isArchKFinite_invariant_nonneg_integral_maximalCompactAtHaar_mul_ne_zero
    (K : Type) [Field K] [NumberField K]
    (β : ↥(maximalCompactAt K ∅) → ℂ) (_hβ : Continuous β)
    (_hβinv : ∀ (m : AdelicGL2 (𝓞 K) K) (_hm : m ∈ adelicBorel (𝓞 K) K) (hmK : m ∈ maximalCompactAt K ∅)
      (k : ↥(maximalCompactAt K ∅)), β (⟨m, hmK⟩ * k) = β k)
    (_hne : ∃ k₀ : ↥(maximalCompactAt K ∅), β k₀ ≠ 0) :
    ∃ f : AdelicGL2 (𝓞 K) K → ℂ, Continuous f ∧ IsArchKFinite K f ∧
      (∀ (m k : AdelicGL2 (𝓞 K) K), m ∈ adelicBorel (𝓞 K) K →
        glFin (𝓞 K) K m = 1 → glFin (𝓞 K) K k = 1 →
        (∀ w : InfinitePlace K, IsRowIsometry (archComponent K w (glArch (𝓞 K) K m))) →
        (∀ w : InfinitePlace K, IsRowIsometry (archComponent K w (glArch (𝓞 K) K k))) →
          f (m * k) = f k) ∧
      (∀ g : AdelicGL2 (𝓞 K) K, 0 ≤ (f g).re ∧ (f g).im = 0) ∧
      ∫ k, f (k : AdelicGL2 (𝓞 K) K) * β k ∂(maximalCompactAtHaar K ∅) ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_isArchKFinite_invariant_nonneg_integral_maximalCompactAtHaar_mul_ne_zero.solution
