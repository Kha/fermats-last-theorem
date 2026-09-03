import Definitions.Def_M4aHerbrand_IdeleClassVocab
import P2M.Util
import P2M.Sol.S_M4aHerbrand_subsingleton_ideleGaloisDescent

set_option autoImplicit false

theorem M4aHerbrand.subsingleton_ideleGaloisDescent
    (R E F : Type*) [CommRing R] [IsDedekindDomain R] [Field E] [Field F]
    [Algebra R F] [IsFractionRing R F] [Algebra E F] :
    Subsingleton (M4aHerbrand.IdeleGaloisDescent R E F) := by p2m_exact_reverting @_root_.P2MW.S_M4aHerbrand_subsingleton_ideleGaloisDescent.solution
