import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_nonempty_pushforward_hom_comp_iso

universe u
open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.nonempty_pushforward_hom_comp_iso
    {X Y Z : Scheme.{u}} (e : X ≅ Y) (f : Y ⟶ Z) (F : X.Modules) :
    Nonempty ((Scheme.Modules.pushforward (e.hom ≫ f)).obj F ≅
      (Scheme.Modules.pushforward f).obj ((Scheme.Modules.pullback e.inv).obj F)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_nonempty_pushforward_hom_comp_iso.solution
