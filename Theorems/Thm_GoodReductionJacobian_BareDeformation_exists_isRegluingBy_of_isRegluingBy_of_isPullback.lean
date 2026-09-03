import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_GoodReductionJacobian_BareDeformation
import Definitions.Def_GoodReductionJacobian_IsRegluingBy
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_BareDeformation_exists_isRegluingBy_of_isRegluingBy_of_isPullback

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld IsLocalRing
open scoped TensorProduct
theorem GoodReductionJacobian.BareDeformation.exists_isRegluingBy_of_isRegluingBy_of_isPullback
    (B' B B₁ : Type) [CommRing B'] [CommRing B] [CommRing B₁] [Algebra B' B₁] [Algebra B B₁]
    (φ : B' →+* B) (hφ : (algebraMap B B₁).comp φ = algebraMap B' B₁)
    {A₁ : Scheme.{0}} {f₁ : A₁ ⟶ Spec (CommRingCat.of B₁)} {L₁ : RelativeGroupLaw B₁ f₁}
    (D₀ : BareDeformation f₁ L₁ B) (D₀' : BareDeformation f₁ L₁ B')
    (h₀ : D₀'.A ⟶ D₀.A) [IsAffineHom h₀]
    (k : D₀.A ⟶ D₀'.A) (hk : k ≫ h₀ = 𝟙 D₀.A)
    (hkc : IsPullback k D₀.f D₀'.f (Spec.map (CommRingCat.ofHom φ))) (hkg : D₀.g ≫ k = D₀'.g)
    (𝒰 : D₀.A.OrderedAffineCover)
    (r : ∀ s : 𝒰.Idx 1, ((↑(𝒰.inter s) : Scheme.{0}) ⟶ ↑((𝒰.comap h₀).inter s)))
    (hr : ∀ s : 𝒰.Idx 1, r s ≫ ((𝒰.comap h₀).inter s).ι = (𝒰.inter s).ι ≫ k)
    (σ : ∀ s : (𝒰.comap h₀).Idx 1, ((↑((𝒰.comap h₀).inter s) : Scheme.{0}) ≅ ↑((𝒰.comap h₀).inter s)))
    (P : BareDeformation f₁ L₁ B') (hP : D₀'.IsRegluingBy (𝒰.comap h₀) σ P)
    (Dφ : BareDeformation f₁ L₁ B) (h : Dφ.A ⟶ P.A)
    (hc : IsPullback h Dφ.f P.f (Spec.map (CommRingCat.ofHom φ))) (hg : Dφ.g ≫ h = P.g) :
    ∃ τ : ∀ s : 𝒰.Idx 1, ((↑(𝒰.inter s) : Scheme.{0}) ≅ ↑(𝒰.inter s)),
      D₀.IsRegluingBy 𝒰 τ Dφ ∧ ∀ s : 𝒰.Idx 1, (τ s).hom ≫ r s = r s ≫ (σ s).hom := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_BareDeformation_exists_isRegluingBy_of_isRegluingBy_of_isPullback.solution
