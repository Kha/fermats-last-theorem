import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechCup
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechOrdered
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_sub_oext_ores_mem_of_od_eq_zero
attribute [-instance] AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableOSub

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.sub_oext_ores_mem_of_od_eq_zero
    {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (CommRingCat.of R)}
    (F : OModulePresheaf π) (K : V.OrderedAffineCover) (n : ℕ) (c : F.ocochain K n) (hc : F.od K n c = 0) :
    c - F.oext K n (F.ores K n c) ∈
      (show Submodule R (F.ocochain K n) from
        match n with
        | 0 => ⊥
        | m + 1 => LinearMap.range (F.od K m)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_sub_oext_ores_mem_of_od_eq_zero.solution
