import Mathlib
import P2M.Util
import Definitions.Def_Compat_Mathlib430
namespace P2MW.S_Rep_nonempty_res_tensor_ofMulAction_iso_of_equiv

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
set_option Elab.async false

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Module"
open scoped Classical

theorem solution
    {k : Type} [CommRing k] {G : Type} [Group G] (C : Subgroup G) (M : Rep.{0} k G)
    {X Y : Type} [MulAction G X] [MulAction G Y]
    (e : X ≃ Y) (he : ∀ (c : C) (x : X), e ((c : G) • x) = (c : G) • e x) :
    Nonempty (Rep.res C.subtype (M ⊗ Rep.ofMulActionFinsupp k G X) ≅ Rep.res C.subtype (M ⊗ Rep.ofMulActionFinsupp k G Y)) := by
  refine ⟨Rep.mkIso (Representation.Equiv.mk
    (TensorProduct.congr (LinearEquiv.refl k M) (Finsupp.domLCongr e)) ?_)⟩
  intro c
  apply TensorProduct.ext'
  intro m f
  have hmap : Finsupp.equivMapDomain e (Finsupp.mapDomain (fun x ↦ (c : G) • x) f) =
      Finsupp.mapDomain (fun y ↦ (c : G) • y) (Finsupp.equivMapDomain e f) := by
    rw [Finsupp.equivMapDomain_eq_mapDomain, Finsupp.equivMapDomain_eq_mapDomain,
      ← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
    congr 1
    funext x
    exact he c x
  simp [Representation.tprod_apply, Representation.ofMulActionFinsupp_def, hmap]
