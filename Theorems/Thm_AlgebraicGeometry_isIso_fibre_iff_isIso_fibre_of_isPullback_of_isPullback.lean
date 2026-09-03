import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isIso_fibre_iff_isIso_fibre_of_isPullback_of_isPullback

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.isIso_fibre_iff_isIso_fibre_of_isPullback_of_isPullback
    {X Y Z X' Y' Z' : Scheme.{0}} (p : Z ⟶ Y) (q : X ⟶ Y) (h : Z ⟶ X) (w : h ≫ q = p)
    (p' : Z' ⟶ Y') (q' : X' ⟶ Y') (h' : Z' ⟶ X') (w' : h' ≫ q' = p')
    (π : Y' ⟶ Y) (πZ : Z' ⟶ Z) (πX : X' ⟶ X)
    (hZ : IsPullback πZ p' p π) (hX : IsPullback πX q' q π) (hh : h' ≫ πX = πZ ≫ h) (y' : Y') :
    IsIso (pullback.map p' (Y'.fromSpecResidueField y') q' (Y'.fromSpecResidueField y') h' (𝟙 _) (𝟙 _)
          (by rw [Category.comp_id, w']) (by rw [Category.comp_id, Category.id_comp])) ↔
      IsIso (pullback.map p (Y.fromSpecResidueField (π.base y')) q (Y.fromSpecResidueField (π.base y')) h (𝟙 _) (𝟙 _)
          (by rw [Category.comp_id, w]) (by rw [Category.comp_id, Category.id_comp])) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isIso_fibre_iff_isIso_fibre_of_isPullback_of_isPullback.solution
