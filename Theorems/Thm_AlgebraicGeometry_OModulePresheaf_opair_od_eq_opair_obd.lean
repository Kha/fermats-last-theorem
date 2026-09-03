import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechCup
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechOrdered
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechOrderedChains
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_opair_od_eq_opair_obd

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.opair_od_eq_opair_obd
    {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (CommRingCat.of R)}
    (F : OModulePresheaf π) (K : V.OrderedAffineCover) {k : ℕ} (t : K.OIdx k) (n : ℕ) (c : F.ocochain K n)
    (x : K.OCh (n + 1)) (hx : ∀ u ∈ x.support, K.OSub u t) :
    F.opair K t (n + 1) (F.od K n c) x = F.opair K t n c (K.obd n x) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_opair_od_eq_opair_obd.solution
