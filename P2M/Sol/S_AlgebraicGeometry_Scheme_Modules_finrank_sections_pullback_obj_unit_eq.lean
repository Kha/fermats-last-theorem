import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_obj_unit_iso_unit
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_finrank_sections_pullback_obj_unit_eq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u
theorem solution
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
      = Module.finrank A Γ(Limits.pullback f (Scheme.TwoAffineOpenCover.specMap R A), ⊤) := by
  letI iA : Algebra A Γ(Limits.pullback f (Scheme.TwoAffineOpenCover.specMap R A), ⊤) :=
    Scheme.TwoAffineOpenCover.algebraOfHom (Limits.pullback.snd f (Scheme.TwoAffineOpenCover.specMap R A)) ⊤
  letI iM := Scheme.TwoAffineOpenCover.moduleSectionsOfHom
      (Limits.pullback.snd f (Scheme.TwoAffineOpenCover.specMap R A))
      ((Scheme.Modules.pullback (Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R A))).obj
        (SheafOfModules.unit X.ringCatSheaf)) ⊤
  obtain ⟨e⟩ := AlgebraicGeometry.Scheme.Modules.nonempty_pullback_obj_unit_iso_unit
    (X := Limits.pullback f (Scheme.TwoAffineOpenCover.specMap R A)) (Y := X)
    (Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R A))

  let L : Γ((Scheme.Modules.pullback (Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R A))).obj
        (SheafOfModules.unit X.ringCatSheaf), ⊤) ≃ₗ[A] Γ(Limits.pullback f (Scheme.TwoAffineOpenCover.specMap R A), ⊤) :=
    { toFun := fun x => (show Γ(SheafOfModules.unit (Limits.pullback f (Scheme.TwoAffineOpenCover.specMap R A)).ringCatSheaf, ⊤) from
        (e.hom.app ⊤) x)
      invFun := fun y => (e.inv.app ⊤) (show Γ(SheafOfModules.unit (Limits.pullback f (Scheme.TwoAffineOpenCover.specMap R A)).ringCatSheaf, ⊤) from y)
      map_add' := fun x y => by
        show (e.hom.app ⊤) (x + y) = (e.hom.app ⊤) x + (e.hom.app ⊤) y
        exact map_add _ x y
      map_smul' := fun a x => by
        show (e.hom.app ⊤) ((algebraMap A Γ(Limits.pullback f (Scheme.TwoAffineOpenCover.specMap R A), ⊤) a) • x)
          = (algebraMap A Γ(Limits.pullback f (Scheme.TwoAffineOpenCover.specMap R A), ⊤) a) • (e.hom.app ⊤) x
        rw [Scheme.Modules.Hom.app_smul]
      left_inv := fun x => by
        show (e.hom.app ⊤ ≫ e.inv.app ⊤) x = x
        rw [← Scheme.Modules.Hom.comp_app, e.hom_inv_id, Scheme.Modules.Hom.id_app]; rfl
      right_inv := fun y => by
        show (e.inv.app ⊤ ≫ e.hom.app ⊤) _ = _
        rw [← Scheme.Modules.Hom.comp_app, e.inv_hom_id, Scheme.Modules.Hom.id_app]; rfl }
  exact ⟨⟨fun _ => Module.Finite.equiv L, fun _ => Module.Finite.equiv L.symm⟩, L.finrank_eq⟩
