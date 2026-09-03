import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_finrank_sections_pullback_obj_unit_eq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.Modules.finrank_sections_pullback_obj_unit_eq
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    (A : Type u) [CommRing A] [Algebra R A] :
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom
      (Limits.pullback.snd f (Scheme.TwoAffineOpenCover.specMap R A))
      ((Scheme.Modules.pullback (Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R A))).obj
        (SheafOfModules.unit X.ringCatSheaf)) ⊤
    letI := Scheme.TwoAffineOpenCover.algebraOfHom (Limits.pullback.snd f (Scheme.TwoAffineOpenCover.specMap R A)) ⊤
    (Module.Finite A Γ((Scheme.Modules.pullback (Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R A))).obj
        (SheafOfModules.unit X.ringCatSheaf), ⊤) ↔
      Module.Finite A Γ(Limits.pullback f (Scheme.TwoAffineOpenCover.specMap R A), ⊤)) ∧
    Module.finrank A Γ((Scheme.Modules.pullback (Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R A))).obj
        (SheafOfModules.unit X.ringCatSheaf), ⊤)
      = Module.finrank A Γ(Limits.pullback f (Scheme.TwoAffineOpenCover.specMap R A), ⊤) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_finrank_sections_pullback_obj_unit_eq.solution
