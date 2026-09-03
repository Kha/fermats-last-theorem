import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Theorems.Thm_AlgebraicGeometry_SchemeHomOver_ext_of_forall_algebraicClosure_point_of_isReduced_of_flat
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_SchemeHomOver_ext_of_forall_point_of_isReduced_of_isAlgClosed

set_option autoImplicit false

universe u

p2m_open "CategoryTheory AlgebraicGeometry P2MW.S_AlgebraicGeometry_SchemeHomOver_ext_of_forall_point_of_isReduced_of_isAlgClosed.AlgebraicGeometry NeronModelInfra"

namespace AlgebraicGeometry p2m_export "AlgebraicGeometry" "LocallyOfFiniteType Spec Spec.map Scheme HasRingHomProperty.of_source_openCover Flat IsReduced IsSeparated Spec.map_id HasRingHomProperty Scheme.ΓSpecIso SchemeHomOver.ext_of_forall_algebraicClosure_point_of_isReduced_of_flat" end AlgebraicGeometry
p2m_open_scoped "AlgebraicGeometry" in

theorem AlgebraicGeometry.flat_of_field (κ : Type u) [Field κ] {X : Scheme.{u}}
    (gX : X ⟶ Spec (CommRingCat.of κ)) : Flat gX := by
  have hF : IsField (Γ(Spec (CommRingCat.of κ), ⊤) : Type u) :=
    MulEquiv.isField (Field.toIsField κ)
      (Scheme.ΓSpecIso (CommRingCat.of κ)).commRingCatIsoToRingEquiv.toMulEquiv
  exact HasRingHomProperty.of_source_openCover (P := @Flat) X.affineCover
    (fun i => RingHom.Flat.of_isField hF _)

theorem solution
    (κ : Type u) [Field κ] [IsAlgClosed κ] {X Y : Scheme.{u}}
    {gX : X ⟶ Spec (CommRingCat.of κ)} {gY : Y ⟶ Spec (CommRingCat.of κ)}
    [LocallyOfFiniteType gX] [IsReduced X] [IsSeparated gY]
    (φ ψ : SchemeHomOver gX gY)
    (h : ∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of κ))) gX, x.1 ≫ φ.1 = x.1 ≫ ψ.1) :
    φ = ψ := by
  haveI : Flat gX := AlgebraicGeometry.flat_of_field κ gX
  apply SchemeHomOver.ext_of_forall_algebraicClosure_point_of_isReduced_of_flat (R := κ) κ κ
    (gY := gX) (gX := gY) φ ψ
  intro x
  have hid : Spec.map (CommRingCat.ofHom (algebraMap κ κ)) = 𝟙 (Spec (CommRingCat.of κ)) := by
    rw [show algebraMap κ κ = RingHom.id κ from rfl, CommRingCat.ofHom_id, Spec.map_id]
  exact h ⟨x.1, by rw [x.2, hid]⟩
