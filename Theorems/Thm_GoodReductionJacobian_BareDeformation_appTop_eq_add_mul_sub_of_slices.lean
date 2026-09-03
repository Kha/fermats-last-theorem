import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_GoodReductionJacobian_BareDeformation
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_BareDeformation_appTop_eq_add_mul_sub_of_slices
attribute [-instance] PresheafOfModules.ExteriorPower.instModulePresheafAb
attribute [-simp] AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.Scheme.Modules.exteriorPower_obj

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld IsLocalRing
  Scheme.TwoAffineOpenCover
open scoped TensorProduct
theorem GoodReductionJacobian.BareDeformation.appTop_eq_add_mul_sub_of_slices
    (B' B B₁ : Type) [CommRing B'] [CommRing B] [CommRing B₁] [Algebra B' B₁] [Algebra B B₁]
    (δ : B →+* B') (p₀ p₁ p₂ : B' →+* B)
    (hp₀δ : p₀.comp δ = RingHom.id B) (hp₁δ : p₁.comp δ = RingHom.id B) (hp₂δ : p₂.comp δ = RingHom.id B)
    (hinj : ∀ x y : B', p₀ x = p₀ y → p₁ x = p₁ y → p₂ x = p₂ y → x = y)
    (hsurj : ∀ b₀ b₁ b₂ : B, algebraMap B B₁ b₀ = algebraMap B B₁ b₁ → algebraMap B B₁ b₁ = algebraMap B B₁ b₂ →
      ∃ x : B', p₀ x = b₀ ∧ p₁ x = b₁ ∧ p₂ x = b₂)
    (al : B) (α : B' →+* B) (hα : ∀ x : B', α x = p₁ x + al * (p₂ x - p₀ x))
    {A₁ : Scheme.{0}} {f₁ : A₁ ⟶ Spec (CommRingCat.of B₁)} {L₁ : RelativeGroupLaw B₁ f₁}
    (D₀ : BareDeformation f₁ L₁ B) (D₀' : BareDeformation f₁ L₁ B')
    (h' : D₀'.A ⟶ D₀.A) [IsAffineHom h'] (hc' : IsPullback h' D₀'.f D₀.f (Spec.map (CommRingCat.ofHom δ)))
    (k₀ k₁ k₂ kα : D₀.A ⟶ D₀'.A)
    (hk₀ : k₀ ≫ h' = 𝟙 D₀.A) (hk₁ : k₁ ≫ h' = 𝟙 D₀.A) (hk₂ : k₂ ≫ h' = 𝟙 D₀.A) (hkα : kα ≫ h' = 𝟙 D₀.A)
    (hk₀f : k₀ ≫ D₀'.f = D₀.f ≫ Spec.map (CommRingCat.ofHom p₀)) (hk₁f : k₁ ≫ D₀'.f = D₀.f ≫ Spec.map (CommRingCat.ofHom p₁))
    (hk₂f : k₂ ≫ D₀'.f = D₀.f ≫ Spec.map (CommRingCat.ofHom p₂)) (hkαf : kα ≫ D₀'.f = D₀.f ≫ Spec.map (CommRingCat.ofHom α))
    (𝒰 : D₀.A.OrderedAffineCover) (hU : ∀ s : 𝒰.Idx 1, IsAffineOpen (𝒰.inter s)) (s : 𝒰.Idx 1)
    (κ₀ κ₁ κ₂ κα : (↑(𝒰.inter s) : Scheme.{0}) ⟶ ↑((𝒰.comap h').inter s))
    (hκ₀ : κ₀ ≫ ((𝒰.comap h').inter s).ι = (𝒰.inter s).ι ≫ k₀) (hκ₁ : κ₁ ≫ ((𝒰.comap h').inter s).ι = (𝒰.inter s).ι ≫ k₁)
    (hκ₂ : κ₂ ≫ ((𝒰.comap h').inter s).ι = (𝒰.inter s).ι ≫ k₂) (hκα : κα ≫ ((𝒰.comap h').inter s).ι = (𝒰.inter s).ι ≫ kα)
    (σ : (↑((𝒰.comap h').inter s) : Scheme.{0}) ≅ ↑((𝒰.comap h').inter s))
    (τ τ' τα : (↑(𝒰.inter s) : Scheme.{0}) ≅ ↑(𝒰.inter s))
    (h₀ : κ₀ ≫ σ.hom = κ₀) (h₁ : τ.hom ≫ κ₁ = κ₁ ≫ σ.hom) (h₂ : τ'.hom ≫ κ₂ = κ₂ ≫ σ.hom) (h₃ : τα.hom ≫ κα = κα ≫ σ.hom) :
    letI := algebraOfHom D₀.f (𝒰.inter s)
    ∀ x : Γ(D₀.A, 𝒰.inter s),
      ((𝒰.inter s).topIso.inv ≫ τα.hom.appTop ≫ (𝒰.inter s).topIso.hom).hom x =
        ((𝒰.inter s).topIso.inv ≫ τ.hom.appTop ≫ (𝒰.inter s).topIso.hom).hom x +
          algebraMap B Γ(D₀.A, 𝒰.inter s) al *
            (((𝒰.inter s).topIso.inv ≫ τ'.hom.appTop ≫ (𝒰.inter s).topIso.hom).hom x - x) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_BareDeformation_appTop_eq_add_mul_sub_of_slices.solution
