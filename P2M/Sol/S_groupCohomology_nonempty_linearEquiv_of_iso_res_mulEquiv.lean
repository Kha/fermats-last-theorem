import Mathlib
import P2M.Util
namespace P2MW.S_groupCohomology_nonempty_linearEquiv_of_iso_res_mulEquiv

set_option autoImplicit false
open CategoryTheory groupCohomology Rep

theorem solution
    {k G H : Type} [CommRing k] [Group G] [Group H]
    (e : G ≃* H) (A : Rep k G) (B : Rep k H) (φ : A ≅ Rep.res e.toMonoidHom B) (n : ℕ) :
    ∃ ψ : groupCohomology A n ≃ₗ[k] groupCohomology B n,
      ∀ x : groupCohomology B n,
        ψ.symm x = (groupCohomology.map e.toMonoidHom (φ.inv : Rep.res e.toMonoidHom B ⟶ A) n).hom x := by
  classical

  have hA : ∀ x : A, Rep.Hom.hom φ.inv (Rep.Hom.hom φ.hom x) = x := by
    intro x
    have h := congrFun (congrArg (fun f : A ⟶ A => ⇑(Rep.Hom.hom f)) φ.hom_inv_id) x
    exact h
  have hB : ∀ x : Rep.res e.toMonoidHom B, Rep.Hom.hom φ.hom (Rep.Hom.hom φ.inv x) = x := by
    intro x
    have h := congrFun (congrArg (fun f : Rep.res e.toMonoidHom B ⟶ Rep.res e.toMonoidHom B => ⇑(Rep.Hom.hom f))
      φ.inv_hom_id) x
    exact h

  haveI hcomp : ∀ i : ℕ, IsIso ((cochainsMap e.toMonoidHom (φ.inv : Rep.res e.toMonoidHom B ⟶ A)).f i) := by
    intro i
    rw [cochainsMap_f]
    haveI h1 : IsIso (ModuleCat.ofHom (LinearMap.funLeft k ↑B fun x : Fin i → G => ⇑e.toMonoidHom ∘ x)) := by
      refine (ConcreteCategory.isIso_iff_bijective _).mpr ?_
      have hinj : Function.Injective (fun x : Fin i → G => ⇑e.toMonoidHom ∘ x) :=
        fun a b h => funext fun j => e.injective (congrFun h j)
      have hsurj : Function.Surjective (fun x : Fin i → G => ⇑e.toMonoidHom ∘ x) :=
        fun y => ⟨fun j => e.symm (y j), funext fun j => e.apply_symm_apply (y j)⟩
      exact ⟨LinearMap.funLeft_injective_of_surjective k _ _ hsurj,
        LinearMap.funLeft_surjective_of_injective k _ _ hinj⟩
    haveI h2 : IsIso (ModuleCat.ofHom ((Rep.Hom.hom (φ.inv : Rep.res e.toMonoidHom B ⟶ A)).compLeft (Fin i → G))) := by
      refine (ConcreteCategory.isIso_iff_bijective _).mpr ?_
      refine Function.bijective_iff_has_inverse.mpr ⟨(Rep.Hom.hom φ.hom).compLeft (Fin i → G), ?_, ?_⟩
      · intro g
        funext j
        exact hB (g j)
      · intro g
        funext j
        exact hA (g j)
    infer_instance
  haveI : IsIso (cochainsMap e.toMonoidHom (φ.inv : Rep.res e.toMonoidHom B ⟶ A)) :=
    HomologicalComplex.Hom.isIso_of_components _
  haveI : IsIso (groupCohomology.map e.toMonoidHom (φ.inv : Rep.res e.toMonoidHom B ⟶ A) n) := by
    show IsIso (HomologicalComplex.homologyMap _ n)
    infer_instance
  refine ⟨(asIso (groupCohomology.map e.toMonoidHom (φ.inv : Rep.res e.toMonoidHom B ⟶ A) n)).toLinearEquiv.symm, ?_⟩
  intro x
  rw [LinearEquiv.symm_symm]
  rfl
