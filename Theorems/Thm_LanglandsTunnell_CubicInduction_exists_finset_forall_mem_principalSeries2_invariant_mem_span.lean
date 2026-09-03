import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_AutomorphicForm_ConstantTerm
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_exists_finset_forall_mem_principalSeries2_invariant_mem_span
set_option autoImplicit false
open MeasureTheory IsDedekindDomain NumberField UnramifiedWhittaker LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction
  AutomorphicForm
open scoped nonZeroDivisors NNReal ENNReal

theorem LanglandsTunnell.CubicInduction.exists_finset_forall_mem_principalSeries2_invariant_mem_span
    (p : HeightOneSpectrum (𝓞 ℚ))
    (θ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ))
    (c : Fin 2 → ℕ)
    (hcθ : ∀ i : Fin 2, ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p (c i), θ i u = 1)
    (U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) (hU : IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ)))) :
    ∃ B : Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ), ∀ f ∈ principalSeries2 p θ,
      (∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), f (g * k) = f g) → f ∈ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ)) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_finset_forall_mem_principalSeries2_invariant_mem_span.solution
