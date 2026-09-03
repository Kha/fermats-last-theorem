import Definitions.Def_EllipticCurve_RubinSilverbergFamily
import P2M.Util
namespace P2MW.S_RubinSilverberg_kleinVHom_one_right

open RubinSilverberg

theorem solution {R : Type*} [CommRing R] (n : R) : kleinVHom n 1 = kleinV n := by
  unfold kleinVHom kleinV; ring
