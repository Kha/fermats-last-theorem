import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArchKFinite
import P2M.Util
import P2M.Sol.S_AutomorphicForm_eq_zero_of_continuous_of_forall_isArchKFinite_integral_maximalCompactAtHaar_mul_eq_zero

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel AutomorphicForm IsDedekindDomain

theorem AutomorphicForm.eq_zero_of_continuous_of_forall_isArchKFinite_integral_maximalCompactAtHaar_mul_eq_zero
    (K : Type) [Field K] [NumberField K]
    (β : ↥(maximalCompactAt K ∅) → ℂ) (_hβ : Continuous β)
    (_h : ∀ f : AdelicGL2 (𝓞 K) K → ℂ, Continuous f → IsArchKFinite K f →
      ∫ k, f (k : AdelicGL2 (𝓞 K) K) * β k ∂(maximalCompactAtHaar K ∅) = 0) :
    β = 0 := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_eq_zero_of_continuous_of_forall_isArchKFinite_integral_maximalCompactAtHaar_mul_eq_zero.solution
