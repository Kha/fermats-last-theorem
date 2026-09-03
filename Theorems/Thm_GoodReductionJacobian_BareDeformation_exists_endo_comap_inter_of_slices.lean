import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_GoodReductionJacobian_BareDeformation
import Definitions.Def_GoodReductionJacobian_IsRegluingBy
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_BareDeformation_exists_endo_comap_inter_of_slices
attribute [-instance] PresheafOfModules.ExteriorPower.instModulePresheafAb
attribute [-simp] AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.Scheme.Modules.exteriorPower_obj

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld IsLocalRing
open scoped TensorProduct

theorem GoodReductionJacobian.BareDeformation.exists_endo_comap_inter_of_slices
    (B' B B₁ : Type) [CommRing B'] [CommRing B] [CommRing B₁] [Algebra B' B₁] [Algebra B B₁]
    (hπ : Function.Surjective (algebraMap B B₁))
    (δ : B →+* B') (hδ : (algebraMap B' B₁).comp δ = algebraMap B B₁)
    (p₀ p₁ p₂ : B' →+* B) (hp₀δ : p₀.comp δ = RingHom.id B) (hp₁δ : p₁.comp δ = RingHom.id B) (hp₂δ : p₂.comp δ = RingHom.id B)
    (hp₀ : (algebraMap B B₁).comp p₀ = algebraMap B' B₁) (hp₁ : (algebraMap B B₁).comp p₁ = algebraMap B' B₁)
    (hp₂ : (algebraMap B B₁).comp p₂ = algebraMap B' B₁)
    (hinj : ∀ x y : B', p₀ x = p₀ y → p₁ x = p₁ y → p₂ x = p₂ y → x = y)
    (hsurj : ∀ b₀ b₁ b₂ : B, algebraMap B B₁ b₀ = algebraMap B B₁ b₁ → algebraMap B B₁ b₁ = algebraMap B B₁ b₂ →
      ∃ x : B', p₀ x = b₀ ∧ p₁ x = b₁ ∧ p₂ x = b₂)
    {A₁ : Scheme.{0}} {f₁ : A₁ ⟶ Spec (CommRingCat.of B₁)} {L₁ : RelativeGroupLaw B₁ f₁}
    (D₀ : BareDeformation f₁ L₁ B) [IsSeparated D₀.f] (D₀' : BareDeformation f₁ L₁ B')
    (h' : D₀'.A ⟶ D₀.A) [IsAffineHom h'] (hc' : IsPullback h' D₀'.f D₀.f (Spec.map (CommRingCat.ofHom δ)))
    (hg' : D₀'.g ≫ h' = D₀.g)
    (k₀ k₁ k₂ : D₀.A ⟶ D₀'.A) (hk₀ : k₀ ≫ h' = 𝟙 D₀.A) (hk₁ : k₁ ≫ h' = 𝟙 D₀.A) (hk₂ : k₂ ≫ h' = 𝟙 D₀.A)
    (hk₀f : k₀ ≫ D₀'.f = D₀.f ≫ Spec.map (CommRingCat.ofHom p₀)) (hk₁f : k₁ ≫ D₀'.f = D₀.f ≫ Spec.map (CommRingCat.ofHom p₁))
    (hk₂f : k₂ ≫ D₀'.f = D₀.f ≫ Spec.map (CommRingCat.ofHom p₂))
    (𝒰 : D₀.A.OrderedAffineCover)
    {n : ℕ} (t : 𝒰.Idx n)
    (α α' : (↑(𝒰.inter t) : Scheme.{0}) ⟶ ↑(𝒰.inter t))
    (hαB : α ≫ (𝒰.inter t).ι ≫ D₀.f = (𝒰.inter t).ι ≫ D₀.f) (hαg : (D₀.g ∣_ 𝒰.inter t) ≫ α = D₀.g ∣_ 𝒰.inter t)
    (hα'B : α' ≫ (𝒰.inter t).ι ≫ D₀.f = (𝒰.inter t).ι ≫ D₀.f) (hα'g : (D₀.g ∣_ 𝒰.inter t) ≫ α' = D₀.g ∣_ 𝒰.inter t) :
    ∃ σ : (↑((𝒰.comap h').inter t) : Scheme.{0}) ⟶ ↑((𝒰.comap h').inter t),
      σ ≫ ((𝒰.comap h').inter t).ι ≫ D₀'.f = ((𝒰.comap h').inter t).ι ≫ D₀'.f ∧
      (D₀'.g ∣_ (𝒰.comap h').inter t) ≫ σ = D₀'.g ∣_ (𝒰.comap h').inter t ∧
      (∀ κ : (↑(𝒰.inter t) : Scheme.{0}) ⟶ ↑((𝒰.comap h').inter t),
        κ ≫ ((𝒰.comap h').inter t).ι = (𝒰.inter t).ι ≫ k₀ → κ ≫ σ = κ) ∧
      (∀ κ : (↑(𝒰.inter t) : Scheme.{0}) ⟶ ↑((𝒰.comap h').inter t),
        κ ≫ ((𝒰.comap h').inter t).ι = (𝒰.inter t).ι ≫ k₁ → α ≫ κ = κ ≫ σ) ∧
      (∀ κ : (↑(𝒰.inter t) : Scheme.{0}) ⟶ ↑((𝒰.comap h').inter t),
        κ ≫ ((𝒰.comap h').inter t).ι = (𝒰.inter t).ι ≫ k₂ → α' ≫ κ = κ ≫ σ) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_BareDeformation_exists_endo_comap_inter_of_slices.solution
