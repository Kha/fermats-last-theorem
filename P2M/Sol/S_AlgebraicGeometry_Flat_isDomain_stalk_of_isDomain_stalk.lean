import Mathlib
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Flat_isDomain_stalk_of_isDomain_stalk

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem solution
    {Y Z : Scheme.{u}} (h : Y ⟶ Z) [Flat h] (y : Y) [IsDomain (Y.presheaf.stalk y)] :
    IsDomain (Z.presheaf.stalk (h y)) := by
  have hflat : (h.stalkMap y).hom.Flat := Flat.stalkMap h y
  letI := (h.stalkMap y).hom.toAlgebra
  haveI : Module.Flat (Z.presheaf.stalk (h y)) (Y.presheaf.stalk y) := hflat
  haveI : IsLocalHom (algebraMap (Z.presheaf.stalk (h y)) (Y.presheaf.stalk y)) := by
    rw [RingHom.algebraMap_toAlgebra]; infer_instance
  haveI : Module.FaithfullyFlat (Z.presheaf.stalk (h y)) (Y.presheaf.stalk y) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hinj : Function.Injective (algebraMap (Z.presheaf.stalk (h y)) (Y.presheaf.stalk y)) :=
    (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance).injective
  exact hinj.isDomain _

