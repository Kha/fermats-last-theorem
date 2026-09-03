import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableModel
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_exists_ringEquiv_stalk_localRing_coe_eq

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicCurve IsLocalRing

namespace KFSL

theorem exists_ringEquiv_stalk_localRing
    {X : Scheme.{0}} [IsIntegral X] {F : Type} [Field F] (φ : F ≃+* X.functionField) (x : X) :
    ∃ e : X.presheaf.stalk x ≃+* ↥(SemistableModel.localRing X φ x),
      ∀ s : X.presheaf.stalk x, ((e s : ↥(SemistableModel.localRing X φ x)) : F) =
        φ.symm (algebraMap (X.presheaf.stalk x) X.functionField s) := by
  let ex : X.presheaf.stalk x →+* F :=
    (φ.symm : X.functionField ≃+* F).toRingHom.comp (algebraMap (X.presheaf.stalk x) X.functionField)
  have hmem : ∀ g : X.presheaf.stalk x, ex g ∈ SemistableModel.localRing X φ x := fun g => ⟨g, rfl⟩
  have hex_inj : Function.Injective ex :=
    φ.symm.injective.comp (IsFractionRing.injective (X.presheaf.stalk x) X.functionField)
  let ψ : X.presheaf.stalk x →+* ↥(SemistableModel.localRing X φ x) := ex.codRestrict _ hmem
  have hψbij : Function.Bijective ψ :=
    ⟨fun a b hab => hex_inj (congrArg Subtype.val hab), by rintro ⟨_, g, rfl⟩; exact ⟨g, rfl⟩⟩
  exact ⟨RingEquiv.ofBijective ψ hψbij, fun s => rfl⟩

theorem ringEquiv_stalk_localRing_base
    {A₀ : Type} [CommRing A₀] {X : Scheme.{0}} [IsIntegral X] (toBase₀ : X ⟶ Spec (CommRingCat.of A₀))
    {F : Type} [Field F] [Algebra A₀ F] (φ : F ≃+* X.functionField)
    (hφ : ∀ a : A₀, φ (algebraMap A₀ F a) = SemistableModel.baseToFunctionField toBase₀ a) (x : X)
    (e : X.presheaf.stalk x ≃+* ↥(SemistableModel.localRing X φ x))
    (he : ∀ s : X.presheaf.stalk x, ((e s : ↥(SemistableModel.localRing X φ x)) : F) =
        φ.symm (algebraMap (X.presheaf.stalk x) X.functionField s)) (a : A₀) :
    ((e ((X.presheaf.germ ⊤ x trivial).hom (toBase₀.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A₀)).inv.hom a))) :
      ↥(SemistableModel.localRing X φ x)) : F) = algebraMap A₀ F a := by
  rw [he, RingEquiv.symm_apply_eq, hφ]
  show (X.presheaf.stalkSpecializes (genericPoint_specializes x)).hom ((X.presheaf.germ ⊤ x trivial).hom _) = _
  rw [← CommRingCat.comp_apply, TopCat.Presheaf.germ_stalkSpecializes]
  rfl

end KFSL

open KFSL in
theorem solution
    (X : Scheme.{0}) [IsIntegral X] {F : Type} [Field F] (φ : F ≃+* X.functionField) (x : X) :
    ∃ e : X.presheaf.stalk x ≃+* ↥(SemistableModel.localRing X φ x),
      ∀ z : X.presheaf.stalk x,
        ((e z : ↥(SemistableModel.localRing X φ x)) : F) = φ.symm (algebraMap (X.presheaf.stalk x) X.functionField z) :=
  KFSL.exists_ringEquiv_stalk_localRing φ x
