import Definitions.Def_EllipticCurve_RubinSilverbergFamily
import P2M.Util
import P2M.Sol.S_RubinSilverberg_kleinVHom_one_right

open RubinSilverberg
theorem RubinSilverberg.kleinVHom_one_right {R : Type*} [CommRing R] (n : R) : kleinVHom n 1 = kleinV n := by p2m_exact_reverting @_root_.P2MW.S_RubinSilverberg_kleinVHom_one_right.solution
