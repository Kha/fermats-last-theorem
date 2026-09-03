import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_AutomorphicForm_ConstantTerm
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_exists_mem_principalSeries2_ne_zero_forall_localLevelOne_mul_eq_of_higherUnitsAt
set_option autoImplicit false
open MeasureTheory IsDedekindDomain NumberField UnramifiedWhittaker LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction
  AutomorphicForm
open scoped nonZeroDivisors NNReal ENNReal

theorem LanglandsTunnell.CubicInduction.exists_mem_principalSeries2_ne_zero_forall_localLevelOne_mul_eq_of_higherUnitsAt
    (p : HeightOneSpectrum (𝓞 ℚ))
    (θ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ))
    (c : Fin 2 → ℕ)
    (hcθ : ∀ i : Fin 2, ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p (c i), θ i u = 1)
    (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥) (b : ℕ)
    (hNb : p.asIdeal ^ b ∣ N ∧ ¬ p.asIdeal ^ (b + 1) ∣ N)
    (hcb : c 0 + c 1 ≤ b) :
    ∃ f ∈ principalSeries2 p θ, f ≠ 0 ∧
      ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), f (g * k) = f g := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_principalSeries2_ne_zero_forall_localLevelOne_mul_eq_of_higherUnitsAt.solution
