import Mathlib
import P2M.Util
namespace P2MW.S_AlgebraicCurve_germToFunctionField_app_eq_of_fromSpecStalk_comp_eq

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicCurve
namespace GlueAux

theorem comp_algebraMap_stalk_eq
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (π : Y ⟶ X)
    (φ : X.functionField →+* Y.functionField)
    (hφπ : Y.fromSpecStalk (genericPoint Y) ≫ π =
      Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk (genericPoint X))
    (y : Y) :
    φ.comp (algebraMap (X.presheaf.stalk (π y)) X.functionField) =
      (algebraMap (Y.presheaf.stalk y) Y.functionField).comp (π.stalkMap y).hom := by
  have eX : CommRingCat.ofHom (φ.comp (algebraMap (X.presheaf.stalk (π y)) X.functionField)) =
      X.presheaf.stalkSpecializes (genericPoint_specializes (π y)) ≫ CommRingCat.ofHom φ := rfl
  have eY : CommRingCat.ofHom ((algebraMap (Y.presheaf.stalk y) Y.functionField).comp (π.stalkMap y).hom) =
      π.stalkMap y ≫ Y.presheaf.stalkSpecializes (genericPoint_specializes y) := rfl
  have key : Spec.map (CommRingCat.ofHom (φ.comp (algebraMap (X.presheaf.stalk (π y)) X.functionField))) =
      Spec.map (CommRingCat.ofHom
        ((algebraMap (Y.presheaf.stalk y) Y.functionField).comp (π.stalkMap y).hom)) := by
    have l1 : Spec.map (CommRingCat.ofHom (φ.comp (algebraMap (X.presheaf.stalk (π y)) X.functionField))) ≫
        X.fromSpecStalk (π y) = Y.fromSpecStalk (genericPoint Y) ≫ π := by
      rw [eX, Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
      exact hφπ.symm
    have l2 : Spec.map (CommRingCat.ofHom
        ((algebraMap (Y.presheaf.stalk y) Y.functionField).comp (π.stalkMap y).hom)) ≫
        X.fromSpecStalk (π y) = Y.fromSpecStalk (genericPoint Y) ≫ π := by
      rw [eY, Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk,
        Scheme.SpecMap_stalkSpecializes_fromSpecStalk_assoc]
    rw [← cancel_mono (X.fromSpecStalk (π y)), l1, l2]
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective key)

end AlgebraicCurve.GlueAux

theorem solution
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (π : Y ⟶ X)
    (φ : X.functionField →+* Y.functionField)
    (hφπ : Y.fromSpecStalk (genericPoint Y) ≫ π =
      Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk (genericPoint X))
    (U : X.Opens) [Nonempty (U : Scheme.{u})] [Nonempty ((π ⁻¹ᵁ U : Y.Opens) : Scheme.{u})] (s : Γ(X, U)) :
    (Y.germToFunctionField (π ⁻¹ᵁ U)).hom (π.app U s) = φ ((X.germToFunctionField U).hom s) := by
  have hη : genericPoint Y ∈ π ⁻¹ᵁ U :=
    ((genericPoint_spec Y).mem_open_set_iff (π ⁻¹ᵁ U).isOpen).mpr (by simpa using ‹Nonempty ((π ⁻¹ᵁ U : Y.Opens) : Scheme.{u})›)
  have hπη : π (genericPoint Y) ∈ U := hη
  have hc := AlgebraicCurve.GlueAux.comp_algebraMap_stalk_eq π φ hφπ (genericPoint Y)

  have hc' : φ.comp (X.presheaf.stalkSpecializes (genericPoint_specializes (π (genericPoint Y)))).hom =
      (Y.presheaf.stalkSpecializes (genericPoint_specializes (genericPoint Y))).hom.comp
        (π.stalkMap (genericPoint Y)).hom := hc
  have e1 : X.germToFunctionField U =
      X.presheaf.germ U (π (genericPoint Y)) hπη ≫
        X.presheaf.stalkSpecializes (genericPoint_specializes (π (genericPoint Y))) :=
    (X.presheaf.germ_stalkSpecializes hπη (genericPoint_specializes _)).symm
  have e2 : (Y.presheaf.stalkSpecializes (genericPoint_specializes (genericPoint Y))).hom = RingHom.id _ := by
    rw [Y.presheaf.stalkSpecializes_refl]; rfl
  have e3 : (π.stalkMap (genericPoint Y)).hom ((X.presheaf.germ U (π (genericPoint Y)) hπη).hom s) =
      (Y.presheaf.germ (π ⁻¹ᵁ U) (genericPoint Y) hπη).hom (π.app U s) := by
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.germ_stalkMap]
  have e1' : (X.germToFunctionField U).hom s =
      (X.presheaf.stalkSpecializes (genericPoint_specializes (π (genericPoint Y)))).hom
        ((X.presheaf.germ U (π (genericPoint Y)) hπη).hom s) := by
    rw [e1]; rfl
  have hcs := congrArg (fun g => g ((X.presheaf.germ U (π (genericPoint Y)) hπη).hom s)) hc'
  simp only [RingHom.comp_apply, e2, RingHom.id_apply, e3] at hcs
  rw [e1', hcs]
