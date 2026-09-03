import Mathlib
import Definitions.Def_AlgebraicGeometry_FramedPolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_isSectionBasis_of_isSectionBasisOn_pullback_id

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {S : Type} [CommRing S] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of S)) (M : X.Modules) {m : ℕ}
    (σ : Fin m → Γ(M, ⊤))
    (h : Scheme.Modules.IsSectionBasisOn f ((Scheme.Modules.pullback (𝟙 X)).obj M) ((𝟙 X) ⁻¹ᵁ ⊤)
      (fun i => Scheme.Modules.pullbackLocalSection (𝟙 X) (σ i))) :
    Scheme.Modules.IsSectionBasis f M σ := by
  classical

  set e : (Scheme.Modules.pullback (𝟙 X)).obj M ⟶ M := (Scheme.Modules.pullbackId X).hom.app M with he
  haveI : IsIso e := by rw [he]; show IsIso ((Scheme.Modules.pullbackId X).app M).hom; infer_instance
  have hcomp : (Scheme.Modules.pullbackPushforwardAdjunction (𝟙 X)).unit.app M ≫
      (Scheme.Modules.pushforward (𝟙 X)).map e = (Scheme.Modules.pushforwardId X).inv.app M := by
    have h0 := Scheme.Modules.conjugateEquiv_pullbackId_hom X
    have := congrArg (fun (t : 𝟭 _ ⟶ _) => t.app M) h0
    simpa [CategoryTheory.conjugateEquiv_apply_app] using this
  have key : ∀ s : Γ(M, ⊤), (Scheme.Modules.Hom.app e ⊤).hom (Scheme.Modules.pullbackLocalSection (𝟙 X) s) = s := by
    intro s
    have h1 := congrArg (fun t => (Scheme.Modules.Hom.app t ⊤).hom s) hcomp
    exact h1

  have hbij : Function.Bijective (Scheme.Modules.Hom.app e ⊤).hom :=
    ConcreteCategory.bijective_of_isIso (Scheme.Modules.Hom.app e ⊤)
  have hfun : (fun c : Fin m → S =>
      ∑ i, ((f.appLE ⊤ ⊤ le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (c i))) • σ i) =
      (Scheme.Modules.Hom.app e ⊤).hom ∘ (fun c : Fin m → S =>
        ∑ i, ((f.appLE ⊤ ⊤ le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (c i))) •
          (show Γ((Scheme.Modules.pullback (𝟙 X)).obj M, ⊤) from Scheme.Modules.pullbackLocalSection (𝟙 X) (σ i))) := by
    funext c
    simp only [Function.comp_apply, map_sum, Scheme.Modules.Hom.app_smul, key]
  show Function.Bijective _
  rw [hfun]
  exact hbij.comp h
