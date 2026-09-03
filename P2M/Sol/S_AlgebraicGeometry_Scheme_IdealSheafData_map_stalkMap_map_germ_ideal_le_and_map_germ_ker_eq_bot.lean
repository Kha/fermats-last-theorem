import Mathlib
import Definitions.Def_AlgebraicCurve_RelCartier
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_map_stalkMap_map_germ_ideal_le_and_map_germ_ker_eq_bot

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace GermFunct

theorem map_stalkMap_map_germ_le {X X' : Scheme.{u}} (f : X' ⟶ X) (I : X.IdealSheafData) (x' : X') (U : X.affineOpens)
    (hU : f.base x' ∈ (U : X.Opens)) (U' : X'.affineOpens) (hU' : x' ∈ (U' : X'.Opens)) (hle : (U' : X'.Opens) ≤ f ⁻¹ᵁ (U : X.Opens)) :
    Ideal.map (f.stalkMap x').hom (Ideal.map (X.presheaf.germ (U : X.Opens) (f.base x') hU).hom (I.ideal U)) ≤
      Ideal.map (X'.presheaf.germ (U' : X'.Opens) x' hU').hom ((I.comap f).ideal U') := by
  rw [Ideal.map_map, Ideal.map_le_iff_le_comap]
  intro a ha
  rw [Ideal.mem_comap]

  have hcomp : ((f.stalkMap x').hom.comp (X.presheaf.germ (U : X.Opens) (f.base x') hU).hom) a =
      (X'.presheaf.germ (U' : X'.Opens) x' hU').hom (f.appLE (U : X.Opens) (U' : X'.Opens) hle a) := by
    rw [RingHom.comp_apply, Scheme.Hom.germ_stalkMap_apply]
    change _ = (X'.presheaf.germ (U' : X'.Opens) x' hU').hom ((f.app (U : X.Opens) ≫ X'.presheaf.map (homOfLE hle).op).hom a)
    rw [CommRingCat.comp_apply, TopCat.Presheaf.germ_res_apply X'.presheaf (homOfLE hle) x' hU']
  rw [hcomp]
  exact Ideal.mem_map_of_mem _ (Scheme.IdealSheafData.IdealHom.appLE_mem_comap_ideal f U U' hle ⟨a, ha⟩)

theorem map_stalkMap_map_germ_ker_eq_bot {C X : Scheme.{u}} (φ : C ⟶ X) (c : C) (U : X.affineOpens)
    (hU : φ.base c ∈ (U : X.Opens)) :
    Ideal.map (φ.stalkMap c).hom (Ideal.map (X.presheaf.germ (U : X.Opens) (φ.base c) hU).hom (φ.ker.ideal U)) = ⊥ := by
  rw [Ideal.map_map, Ideal.map_eq_bot_iff_le_ker]
  intro a ha
  rw [RingHom.mem_ker, RingHom.comp_apply, Scheme.Hom.germ_stalkMap_apply]
  have h0 : (φ.app (U : X.Opens)).hom a = 0 := RingHom.mem_ker.mp (Scheme.Hom.ideal_ker_le φ U ha)
  rw [h0, map_zero]

end GermFunct

theorem solution :

    (∀ {X X' : Scheme.{u}} (f : X' ⟶ X) (I : X.IdealSheafData) (x' : X') (U : X.affineOpens) (hU : f.base x' ∈ (U : X.Opens))
        (U' : X'.affineOpens) (hU' : x' ∈ (U' : X'.Opens)) (hle : (U' : X'.Opens) ≤ f ⁻¹ᵁ (U : X.Opens)),
        Ideal.map (f.stalkMap x').hom (Ideal.map (X.presheaf.germ (U : X.Opens) (f.base x') hU).hom (I.ideal U)) ≤
          Ideal.map (X'.presheaf.germ (U' : X'.Opens) x' hU').hom ((I.comap f).ideal U')) ∧
    (∀ {C X : Scheme.{u}} (φ : C ⟶ X) (c : C) (U : X.affineOpens) (hU : φ.base c ∈ (U : X.Opens)),
        Ideal.map (φ.stalkMap c).hom (Ideal.map (X.presheaf.germ (U : X.Opens) (φ.base c) hU).hom (φ.ker.ideal U)) = ⊥) :=
  ⟨fun f I x' U hU U' hU' hle => GermFunct.map_stalkMap_map_germ_le f I x' U hU U' hU' hle,
   fun φ c U hU => GermFunct.map_stalkMap_map_germ_ker_eq_bot φ c U hU⟩
