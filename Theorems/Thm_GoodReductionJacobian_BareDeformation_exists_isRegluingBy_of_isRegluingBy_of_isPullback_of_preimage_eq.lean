import Mathlib
import Definitions.Def_GoodReductionJacobian_BareDeformation
import Definitions.Def_GoodReductionJacobian_IsRegluingBy
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_BareDeformation_exists_isRegluingBy_of_isRegluingBy_of_isPullback_of_preimage_eq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.BareDeformation.exists_isRegluingBy_of_isRegluingBy_of_isPullback_of_preimage_eq
    {S : Type} [CommRing S] {Aₛ : Scheme.{0}} {fₛ : Aₛ ⟶ Spec (CommRingCat.of S)} {Lₛ : RelativeGroupLaw S fₛ}
    {B : Type} [CommRing B] [Algebra B S]
    (D₀ : BareDeformation fₛ Lₛ B) (𝒰 : D₀.A.OrderedAffineCover)
    (τ : ∀ s : 𝒰.Idx 1, ((↑(𝒰.inter s) : Scheme.{0}) ≅ ↑(𝒰.inter s)))
    (D : BareDeformation fₛ Lₛ B) (hD : D₀.IsRegluingBy 𝒰 τ D)
    (φ : B →+* B)
    (k₀ : D₀.A ⟶ D₀.A) (hk₀ : IsPullback k₀ D₀.f D₀.f (Spec.map (CommRingCat.ofHom φ)))
    (hk₀g : D₀.g ≫ k₀ = D₀.g) (hk₀U : ∀ a : 𝒰.ι, k₀ ⁻¹ᵁ 𝒰.U a = 𝒰.U a)
    (Dφ : BareDeformation fₛ Lₛ B) (h : Dφ.A ⟶ D.A)
    (hh : IsPullback h Dφ.f D.f (Spec.map (CommRingCat.ofHom φ))) (hhg : Dφ.g ≫ h = D.g)
    (hle : ∀ s : 𝒰.Idx 1, 𝒰.inter s ≤ k₀ ⁻¹ᵁ 𝒰.inter s) :
    ∃ τ' : ∀ s : 𝒰.Idx 1, ((↑(𝒰.inter s) : Scheme.{0}) ≅ ↑(𝒰.inter s)),
      (∀ s : 𝒰.Idx 1, (τ' s).hom ≫ k₀.resLE (𝒰.inter s) (𝒰.inter s) (hle s) =
        k₀.resLE (𝒰.inter s) (𝒰.inter s) (hle s) ≫ (τ s).hom) ∧
      D₀.IsRegluingBy 𝒰 τ' Dφ := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_BareDeformation_exists_isRegluingBy_of_isRegluingBy_of_isPullback_of_preimage_eq.solution
