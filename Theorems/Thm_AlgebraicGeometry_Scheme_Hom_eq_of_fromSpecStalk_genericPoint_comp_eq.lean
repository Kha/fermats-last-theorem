import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Hom_eq_of_fromSpecStalk_genericPoint_comp_eq

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry Opposite

theorem AlgebraicGeometry.Scheme.Hom.eq_of_fromSpecStalk_genericPoint_comp_eq
    {U H S : Scheme.{u}} [IsIntegral U] (sU : U ⟶ S) (sH : H ⟶ S) [IsSeparated sH]
    (f g : U ⟶ H) (hf : f ≫ sH = sU) (hg : g ≫ sH = sU)
    (h : U.fromSpecStalk (genericPoint U) ≫ f = U.fromSpecStalk (genericPoint U) ≫ g) :
    f = g := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Hom_eq_of_fromSpecStalk_genericPoint_comp_eq.solution
