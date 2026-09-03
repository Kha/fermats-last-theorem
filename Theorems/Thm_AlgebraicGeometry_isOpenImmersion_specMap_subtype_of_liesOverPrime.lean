import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isOpenImmersion_specMap_subtype_of_liesOverPrime

set_option autoImplicit false

open AlgebraicGeometry

theorem AlgebraicGeometry.isOpenImmersion_specMap_subtype_of_liesOverPrime
    (O : ValuationSubring (AlgebraicClosure ℚ)) (p : ℕ) (hp : p.Prime) (hO : O.LiesOverPrime p) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom O.subtype)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isOpenImmersion_specMap_subtype_of_liesOverPrime.solution
