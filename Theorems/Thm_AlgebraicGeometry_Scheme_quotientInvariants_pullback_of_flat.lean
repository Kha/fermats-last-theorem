import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_quotientInvariants_pullback_of_flat

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.quotientInvariants_pullback_of_flat
    {B₀ 𝒪 : Type} [CommRing B₀] [CommRing 𝒪] (i : B₀ →+* 𝒪) (hi : Flat (Spec.map (CommRingCat.ofHom i)))
    {M X : Scheme.{0}} (πM : M ⟶ Spec (CommRingCat.of B₀)) (πX : X ⟶ Spec (CommRingCat.of B₀))
    (π : M ⟶ X) (hπX : π ≫ πX = πM)
    {H : Type} [Group H] [Finite H] (ρ : H →* Aut M) (hover : ∀ h : H, (ρ h).hom ≫ πM = πM)
    (hπ : ∀ h : H, (ρ h).hom ≫ π = π)
    (hint : IsIntegralHom π) (haff : IsAffineHom π) (hsurj : Function.Surjective π.base)
    (hsec : ∀ V : X.Opens, Function.Injective (π.app V))
    (hinv : ∀ V : X.Opens, Set.range (π.app V) =
      {s | ∀ h : H, (ρ h).hom.appLE (π ⁻¹ᵁ V) (π ⁻¹ᵁ V) (by rw [← Scheme.Hom.comp_preimage, hπ h]) s = s})

    {M' X' : Scheme.{0}} (πM' : M' ⟶ Spec (CommRingCat.of 𝒪)) (πX' : X' ⟶ Spec (CommRingCat.of 𝒪))
    (gM : M' ⟶ M) (hgM : IsPullback gM πM' πM (Spec.map (CommRingCat.ofHom i)))
    (gX : X' ⟶ X) (hgX : IsPullback gX πX' πX (Spec.map (CommRingCat.ofHom i)))
    (π' : M' ⟶ X') (hπX' : π' ≫ πX' = πM') (hπg : π' ≫ gX = gM ≫ π)
    (ρ' : H →* Aut M') (hover' : ∀ h : H, (ρ' h).hom ≫ πM' = πM') (hρg : ∀ h : H, (ρ' h).hom ≫ gM = gM ≫ (ρ h).hom)
    (hπ' : ∀ h : H, (ρ' h).hom ≫ π' = π') :
    IsIntegralHom π' ∧ IsAffineHom π' ∧ Function.Surjective π'.base ∧
    (∀ V' : X'.Opens, Function.Injective (π'.app V')) ∧
    (∀ V' : X'.Opens, Set.range (π'.app V') =
      {s | ∀ h : H, (ρ' h).hom.appLE (π' ⁻¹ᵁ V') (π' ⁻¹ᵁ V') (by rw [← Scheme.Hom.comp_preimage, hπ' h]) s = s}) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_quotientInvariants_pullback_of_flat.solution
