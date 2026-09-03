import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_HaarQuotient
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AdelicDock_LocalEmbedding
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_exists_spherical_mem_principalSeries2_of_unramified

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory AutomorphicForm LanglandsTunnell.TateLocal
  LanglandsTunnell.CubicInduction
open UnramifiedWhittaker

theorem LanglandsTunnell.CubicInduction.exists_spherical_mem_principalSeries2_of_unramified
    (v : HeightOneSpectrum (𝓞 ℚ))
    (χ : Fin 2 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (hχ : ∀ i, ∀ u : (v.adicCompletion ℚ)ˣ, Valued.v (u : v.adicCompletion ℚ) = 1 → χ i u = 1) :
    ∃ f : GL (Fin 2) (v.adicCompletion ℚ) → ℂ, f ∈ principalSeries2 v χ ∧
      (∀ (k g : GL (Fin 2) (v.adicCompletion ℚ)),
        k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ → f (g * k) = f g) ∧
      f 1 = 1 := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_spherical_mem_principalSeries2_of_unramified.solution
