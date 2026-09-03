import Definitions.Def_LanglandsTunnell_CubicInduction_Carrier
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_isOpen_localMaximalCompact3

set_option autoImplicit false

open IsDedekindDomain

theorem
LanglandsTunnell.CubicInduction.isOpen_localMaximalCompact3
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    (v : HeightOneSpectrum R) :
    IsOpen ((localMaximalCompact3 R K v : Subgroup (GL (Fin 3) (v.adicCompletion K))) :
      Set (GL (Fin 3) (v.adicCompletion K))) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_isOpen_localMaximalCompact3.solution
