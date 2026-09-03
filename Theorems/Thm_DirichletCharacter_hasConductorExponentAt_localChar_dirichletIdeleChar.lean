import Definitions.Def_DirichletCharacter_DirichletIdeleChar
import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt
import Definitions.Def_NumberField_TateGlobalZeta
import P2M.Util
import P2M.Sol.S_DirichletCharacter_hasConductorExponentAt_localChar_dirichletIdeleChar

set_option autoImplicit false

open NumberField IsDedekindDomain NumberField.TateGlobal LanglandsTunnell.TateLocal

theorem DirichletCharacter.hasConductorExponentAt_localChar_dirichletIdeleChar
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive)
    (v : HeightOneSpectrum (RingOfIntegers ℚ)) :
    HasConductorExponentAt ℚ v (localChar (dirichletIdeleChar χ) v)
      (N.factorization (Ideal.absNorm v.asIdeal)) := by p2m_exact_reverting @_root_.P2MW.S_DirichletCharacter_hasConductorExponentAt_localChar_dirichletIdeleChar.solution
