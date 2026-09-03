import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_finite_schemeHomOver_of_isFinite

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

namespace S17Glue

theorem finite_schemeHomOver_of_isFinite
    {S N : Scheme.{u}} (p : N ⟶ S) [IsFinite p]
    (k : Type u) [Field k] (t : Spec (CommRingCat.of k) ⟶ S) :
    Finite (SchemeHomOver t p) := by

  let F := pullback p t
  let q : F ⟶ Spec (CommRingCat.of k) := pullback.snd p t
  haveI : IsFinite q := inferInstance
  haveI : IsAffine F := isAffine_of_isAffineHom q

  let Sec := {s : Spec (CommRingCat.of k) ⟶ F // s ≫ q = 𝟙 _}

  let toSec : SchemeHomOver t p → Sec := fun x =>
    ⟨pullback.lift x.1 (𝟙 _) (by rw [x.2, Category.id_comp]), pullback.lift_snd _ _ _⟩
  have htoSec : Function.Injective toSec := by
    intro x y hxy
    apply Subtype.ext
    have := congrArg (fun s : Sec => s.1 ≫ pullback.fst p t) hxy
    simp only [toSec, pullback.lift_fst] at this
    exact this

  let A : CommRingCat.{u} := Γ(F, ⊤)
  let ι : CommRingCat.of k ⟶ A := (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ q.appTop
  let β : Sec → (A ⟶ CommRingCat.of k) := fun s => s.1.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of k)).hom
  have hβι : ∀ s : Sec, ι ≫ β s = 𝟙 _ := by
    intro s
    simp only [ι, β, Category.assoc]
    rw [← Category.assoc q.appTop, ← Scheme.Hom.comp_appTop, s.2, Scheme.Hom.id_appTop,
      Category.id_comp, Iso.inv_hom_id]
  have hβ : Function.Injective β := by
    intro s₁ s₂ h
    apply Subtype.ext
    apply ext_of_isAffine
    have := congrArg (fun m => m ≫ (Scheme.ΓSpecIso (CommRingCat.of k)).inv) h
    simpa [β] using this

  haveI : IsArtinianRing A := by

    have hfin : q.appTop.hom.Finite := q.finite_appTop
    letI : Algebra k A := ι.hom.toAlgebra
    haveI : Module.Finite k A := by
      have : ι.hom.Finite := by
        have e : ι.hom = q.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom := by
          simp [ι, CommRingCat.hom_comp]
        rw [e]
        exact RingHom.Finite.comp hfin (RingHom.Finite.of_surjective _
          (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.symm.surjective)
      exact this
    exact IsArtinianRing.of_finite k A
  have hβι' : ∀ (s : Sec) (z : k), (β s).hom (ι.hom z) = z := by
    intro s z
    have := congrArg (fun m => m.hom z) (hβι s)
    simp only [CommRingCat.hom_comp, CommRingCat.hom_id, RingHom.comp_apply, RingHom.id_apply] at this
    exact this
  let κ : Sec → PrimeSpectrum A := fun s => ⟨RingHom.ker (β s).hom, RingHom.ker_isPrime _⟩
  have hκ : Function.Injective κ := by
    intro s₁ s₂ h
    apply hβ
    have hk : RingHom.ker (β s₁).hom = RingHom.ker (β s₂).hom := congrArg PrimeSpectrum.asIdeal h
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    have h1 : a - ι.hom ((β s₁).hom a) ∈ RingHom.ker (β s₁).hom := by
      rw [RingHom.mem_ker, map_sub, hβι', sub_self]
    rw [hk, RingHom.mem_ker, map_sub, sub_eq_zero, hβι'] at h1
    exact h1.symm
  haveI : Finite Sec := Finite.of_injective κ hκ
  exact Finite.of_injective toSec htoSec

end S17Glue

theorem solution
    {S N : Scheme.{u}} (p : N ⟶ S) [IsFinite p]
    (k : Type u) [Field k] (t : Spec (CommRingCat.of k) ⟶ S) :
    Finite (SchemeHomOver t p) :=
  S17Glue.finite_schemeHomOver_of_isFinite p k t
