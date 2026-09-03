import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ValuationSubring_isLocalization_away_natCast_of_liesOverPrime
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_isOpenImmersion_specMap_subtype_of_liesOverPrime

set_option autoImplicit false

open AlgebraicGeometry

theorem solution
    (O : ValuationSubring (AlgebraicClosure ℚ)) (p : ℕ) (hp : p.Prime) (hO : O.LiesOverPrime p) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom O.subtype)) := by
  haveI := ValuationSubring.isLocalization_away_natCast_of_liesOverPrime O p hp hO
  exact IsOpenImmersion.of_isLocalization ((p : ℕ) : ↥O)
