import Mathlib
import Definitions.Def_AlgebraicGeometry_DescentCharacter
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_DescentCharacter_hasValue_pullback_mapIso_one

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry AlgebraicGeometry.DescentCharacter

namespace KcDescCharOne

variable {X Y : Scheme.{u}} {R : Type u} [CommRing R]

theorem isBaseScalar_id (f : X ⟶ Spec (CommRingCat.of R)) (M : X.Modules) : IsBaseScalar f (𝟙 M) 1 := by
  intro U s
  rw [Scheme.Modules.Hom.id_app, CategoryTheory.id_apply, baseSection_one, one_smul]

theorem translateIso_mapIso {T : X ⟶ X} {q : X ⟶ Y} (h : T ≫ q = q) {N M : Y.Modules} (ι : N ≅ M) :
    translateIso h ((Scheme.Modules.pullback q).mapIso ι) = (Scheme.Modules.pullback q).mapIso ι := by
  ext : 1
  have nat := (transportNatIso h).hom.naturality ι.hom

  simp only [translateIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, ← transportNatIso_app]
  have nat' : (Scheme.Modules.pullback T).map ((Scheme.Modules.pullback q).map ι.hom) ≫
      (transportNatIso h).hom.app M = (transportNatIso h).hom.app N ≫ (Scheme.Modules.pullback q).map ι.hom := nat
  rw [Iso.inv_comp_eq, Iso.app_hom, Iso.app_hom]
  exact nat'

theorem hasValue_pullback_mapIso_one (f : X ⟶ Spec (CommRingCat.of R))
    {T : X ⟶ X} {q : X ⟶ Y} (h : T ≫ q = q) {N M : Y.Modules} (ι : N ≅ M) :
    HasValue f h ((Scheme.Modules.pullback q).mapIso ι) 1 := by
  unfold HasValue discrepancy
  rw [translateIso_mapIso, Iso.symm_self_id]
  exact isBaseScalar_id f _

end KcDescCharOne

theorem solution
    {X Y : Scheme.{u}} {R : Type u} [CommRing R] (f : X ⟶ Spec (CommRingCat.of R))
    {T : X ⟶ X} {q : X ⟶ Y} (h : T ≫ q = q) {N M : Y.Modules} (ι : N ≅ M) :
    HasValue f h ((Scheme.Modules.pullback q).mapIso ι) 1 :=
  KcDescCharOne.hasValue_pullback_mapIso_one f h ι
