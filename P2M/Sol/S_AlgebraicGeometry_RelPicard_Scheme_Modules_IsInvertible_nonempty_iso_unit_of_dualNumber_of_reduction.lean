import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_unit_of_pullback_squareZero
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_RelPicard_Scheme_Modules_IsInvertible_nonempty_iso_unit_of_dualNumber_of_reduction
attribute [-simp] AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    (Cr : Type u) [CommRing Cr] (M : (Spec (.of (DualNumber Cr))).Modules) (hM : Scheme.Modules.IsInvertible M)
    (h0 : Nonempty ((Scheme.Modules.pullback
      (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom Cr Cr Cr).toRingHom))).obj M ≅
        SheafOfModules.unit.{u} (Spec (.of Cr)).ringCatSheaf)) :
    Nonempty (M ≅ SheafOfModules.unit.{u} (Spec (.of (DualNumber Cr))).ringCatSheaf) := by
  obtain ⟨e0⟩ := h0
  set fst : DualNumber Cr →+* Cr := (TrivSqZeroExt.fstHom Cr Cr Cr).toRingHom with hfst
  let I : Ideal (DualNumber Cr) := RingHom.ker fst
  have hmem : ∀ a : DualNumber Cr, a ∈ I ↔ a.fst = 0 := fun a => Iff.rfl

  have hI : I ^ 2 = ⊥ := by
    rw [pow_two, eq_bot_iff, Ideal.mul_le]
    intro a ha b hb
    rw [hmem] at ha hb
    rw [Submodule.mem_bot]
    refine TrivSqZeroExt.ext ?_ ?_
    · simp [TrivSqZeroExt.fst_mul, ha]
    · simp [TrivSqZeroExt.snd_mul, ha, hb]

  have hsurj : Function.Surjective fst := fun c => ⟨TrivSqZeroExt.inl c, TrivSqZeroExt.fst_inl Cr c⟩
  let q : (DualNumber Cr ⧸ I) ≃+* Cr := RingHom.quotientKerEquivOfSurjective hsurj
  have hq : ∀ x, q (Ideal.Quotient.mk I x) = fst x := fun x => RingHom.kerLift_mk fst x
  have hring : q.symm.toRingHom.comp fst = Ideal.Quotient.mk I :=
    RingHom.ext fun x => (RingEquiv.symm_apply_eq q).mpr (hq x).symm

  have hπ : Spec.map (CommRingCat.ofHom q.symm.toRingHom) ≫ Spec.map (CommRingCat.ofHom fst) =
      Spec.map (CommRingCat.ofHom (R := DualNumber Cr) (S := DualNumber Cr ⧸ I) (Ideal.Quotient.mk I)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hring]

  have h : Nonempty ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).obj M ≅
      SheafOfModules.unit (Spec (CommRingCat.of (DualNumber Cr ⧸ I))).ringCatSheaf) :=
    ⟨(Scheme.Modules.pullbackCongr hπ.symm).app M ≪≫
      ((Scheme.Modules.pullbackComp _ _).app M).symm ≪≫
      (Scheme.Modules.pullback _).mapIso e0 ≪≫
      Scheme.Modules.pullbackUnitIso _⟩

  exact _root_.AlgebraicGeometry.Scheme.Modules.IsInvertible.nonempty_iso_unit_of_pullback_squareZero I hI M hM h
