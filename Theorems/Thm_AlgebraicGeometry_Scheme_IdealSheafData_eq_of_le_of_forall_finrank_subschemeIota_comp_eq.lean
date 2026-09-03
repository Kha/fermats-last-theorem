import Mathlib
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_IdealSheafData_eq_of_le_of_forall_finrank_subschemeIota_comp_eq

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

theorem AlgebraicGeometry.Scheme.IdealSheafData.eq_of_le_of_forall_finrank_subschemeIota_comp_eq
    {X S : Scheme.{u}} (p : X ⟶ S) (I J : X.IdealSheafData) (hIJ : I ≤ J)
    [IsFinite (I.subschemeι ≫ p)] [Flat (I.subschemeι ≫ p)] [LocallyOfFinitePresentation (I.subschemeι ≫ p)]
    [Flat (J.subschemeι ≫ p)] [LocallyOfFinitePresentation (J.subschemeι ≫ p)]
    (h : ∀ s : S, (J.subschemeι ≫ p).finrank s = (I.subschemeι ≫ p).finrank s) :
    I = J := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_eq_of_le_of_forall_finrank_subschemeIota_comp_eq.solution
