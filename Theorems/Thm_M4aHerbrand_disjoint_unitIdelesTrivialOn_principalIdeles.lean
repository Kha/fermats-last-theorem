import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import P2M.Util
import P2M.Sol.S_M4aHerbrand_disjoint_unitIdelesTrivialOn_principalIdeles

set_option autoImplicit false
open NumberField IsDedekindDomain M4aHerbrand CategoryTheory
theorem M4aHerbrand.disjoint_unitIdelesTrivialOn_principalIdeles
    (F : Type) [Field F] [NumberField F] (T : Set (HeightOneSpectrum (𝓞 F))) :
    Disjoint (unitIdelesTrivialOn (𝓞 F) F T) (principalIdeles (𝓞 F) F) := by p2m_exact_reverting @_root_.P2MW.S_M4aHerbrand_disjoint_unitIdelesTrivialOn_principalIdeles.solution
