import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechCup
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechOrdered
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechOrderedChains
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_OrderedAffineCover_oSub_of_mem_support_ohom

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.OrderedAffineCover.oSub_of_mem_support_ohom
    {V : Scheme.{u}} (K : V.OrderedAffineCover) (n : ℕ) (σ : K.OIdx n) (u : K.OIdx (n + 1))
    (hu : u ∈ (K.ohom n σ).support) : K.OSub u σ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_OrderedAffineCover_oSub_of_mem_support_ohom.solution
