import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_IdealSheafData_isFinite_and_flat_and_finrank_subscheme_comap_comp_eq_of_isPullback

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.IdealSheafData.isFinite_and_flat_and_finrank_subscheme_comap_comp_eq_of_isPullback
    {X Y S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) (y : Y ⟶ T) (bc : Y ⟶ X)
    (H : IsPullback bc y f g) [IsLocallyNoetherian S] [PreconnectedSpace S]
    (I : X.IdealSheafData) [IsFinite (I.subschemeι ≫ f)] [Flat (I.subschemeι ≫ f)] :
    IsFinite ((I.comap bc).subschemeι ≫ y) ∧ Flat ((I.comap bc).subschemeι ≫ y) ∧
      ∀ (t : T) (s : S), ((I.comap bc).subschemeι ≫ y).finrank t = (I.subschemeι ≫ f).finrank s := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_isFinite_and_flat_and_finrank_subscheme_comap_comp_eq_of_isPullback.solution
