import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_isOpen_congruenceK1

set_option autoImplicit false

open Matrix IsDedekindDomain

theorem
LanglandsTunnell.CubicInduction.isOpen_congruenceK1
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    (v : HeightOneSpectrum R) (c : ℕ) :
    IsOpen (congruenceK1 R K v c) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_isOpen_congruenceK1.solution
