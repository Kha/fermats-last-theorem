import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_ker_fiberIota_stalkMap_eq_maximalIdeal_map
attribute [-instance] kmfloorsGlue_int_three_isPrime kmfloorsGlue_int_bot_isPrime

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.ker_fiberIota_stalkMap_eq_maximalIdeal_map
    {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R))
    (s : Spec (CommRingCat.of R)) (q : f.fiber s) :
    RingHom.ker ((f.fiberι s).stalkMap q).hom =
      (IsLocalRing.maximalIdeal
        ((Spec (CommRingCat.of R)).presheaf.stalk (f.base ((f.fiberι s).base q)))).map
        (f.stalkMap ((f.fiberι s).base q)).hom := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_ker_fiberIota_stalkMap_eq_maximalIdeal_map.solution
