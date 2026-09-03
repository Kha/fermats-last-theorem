import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence
import Definitions.Def_AdelicDock_LocalEmbedding
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_iotaGL_mem_localMaximalCompact3_of_mem_localLevelOne

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField

theorem LanglandsTunnell.CubicInduction.iotaGL_mem_localMaximalCompact3_of_mem_localLevelOne
    (v : HeightOneSpectrum (𝓞 ℚ)) {g : GL (Fin 2) (v.adicCompletion ℚ)}
    (hg : g ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤) :
    iotaGL g ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_iotaGL_mem_localMaximalCompact3_of_mem_localLevelOne.solution
