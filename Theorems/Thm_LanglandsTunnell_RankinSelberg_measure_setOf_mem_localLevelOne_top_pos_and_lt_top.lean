import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AdelicDock_LocalEmbedding
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_RankinSelberg_measure_setOf_mem_localLevelOne_top_pos_and_lt_top

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm MeasureTheory

theorem
    LanglandsTunnell.RankinSelberg.measure_setOf_mem_localLevelOne_top_pos_and_lt_top
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    letI := localGLBorel ℚ v
    ∀ (μN : Measure ↥((unipotentGL2Hom (R := v.adicCompletion ℚ)).range)) [μN.IsHaarMeasure],
      0 < μN {x | (x : GL (Fin 2) (v.adicCompletion ℚ)) ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤} ∧
        μN {x | (x : GL (Fin 2) (v.adicCompletion ℚ)) ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤} < ⊤ := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_RankinSelberg_measure_setOf_mem_localLevelOne_top_pos_and_lt_top.solution
