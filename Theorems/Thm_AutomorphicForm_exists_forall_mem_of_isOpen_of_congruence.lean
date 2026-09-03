import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_CubicInduction_IotaTorus
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_forall_mem_of_isOpen_of_congruence

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField AutomorphicForm UnramifiedWhittaker
  LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

theorem AutomorphicForm.exists_forall_mem_of_isOpen_of_congruence
    (p : HeightOneSpectrum (𝓞 ℚ))
    (U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) (hU : IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ)))) :
    ∃ b : ℕ, ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤,
      (∀ i j : Fin 2, Valued.v ((((k : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) - 1) i j) ≤
        WithZero.exp (-(b : ℤ))) → k ∈ U := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_forall_mem_of_isOpen_of_congruence.solution
