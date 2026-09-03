import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_finite_schemeHomOver_of_isFinite

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

universe u

theorem AlgebraicGeometry.finite_schemeHomOver_of_isFinite
    {S N : Scheme.{u}} (p : N ⟶ S) [IsFinite p]
    (k : Type u) [Field k] (t : Spec (CommRingCat.of k) ⟶ S) :
    Finite (SchemeHomOver t p) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_finite_schemeHomOver_of_isFinite.solution
