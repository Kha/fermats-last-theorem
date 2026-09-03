import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_iotaGL_mem_congruenceK1_iff

set_option autoImplicit false

open Matrix IsDedekindDomain

theorem
LanglandsTunnell.CubicInduction.iotaGL_mem_congruenceK1_iff
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    (v : HeightOneSpectrum R) (c : ℕ) (g : GL (Fin 2) (v.adicCompletion K)) :
    iotaGL g ∈ congruenceK1 R K v c ↔ iotaGL g ∈ localMaximalCompact3 R K v := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_iotaGL_mem_congruenceK1_iff.solution
