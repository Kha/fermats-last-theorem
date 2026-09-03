import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechCup
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechOrdered
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechOrderedChains
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_res_opair

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.res_opair
    {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (CommRingCat.of R)}
    (F : OModulePresheaf π) (K : V.OrderedAffineCover) {k k' : ℕ} (t : K.OIdx k) (t' : K.OIdx k') (htt : K.OSub t' t)
    (n : ℕ) (c : F.ocochain K n) (x : K.OCh n) (hx : ∀ u ∈ x.support, K.OSub u t') :
    F.res (K.ointer_le_ointer_of_oSub htt) (F.opair K t' n c x) = F.opair K t n c x := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_res_opair.solution
