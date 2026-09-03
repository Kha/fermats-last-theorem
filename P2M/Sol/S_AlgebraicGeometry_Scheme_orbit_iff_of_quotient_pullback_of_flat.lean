import Mathlib
import Theorems.Thm_AlgebraicGeometry_Scheme_quotientInvariants_pullback_of_flat
import Theorems.Thm_AlgebraicGeometry_Scheme_orbit_iff_of_isAffineHom_of_invariants
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Scheme_orbit_iff_of_quotient_pullback_of_flat

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {B₀ 𝒪 : Type} [CommRing B₀] [CommRing 𝒪] (i : B₀ →+* 𝒪) (hi : Flat (Spec.map (CommRingCat.ofHom i)))
    {M X : Scheme.{0}} (πM : M ⟶ Spec (CommRingCat.of B₀)) (πX : X ⟶ Spec (CommRingCat.of B₀))
    (π : M ⟶ X) (hπX : π ≫ πX = πM)
    {H : Type} [Group H] [Finite H] (ρ : H →* Aut M) (hover : ∀ h : H, (ρ h).hom ≫ πM = πM)
    (hπ : ∀ h : H, (ρ h).hom ≫ π = π)
    (hint : IsIntegralHom π) (haff : IsAffineHom π) (hsurj : Function.Surjective π.base)
    (horbit : ∀ x x' : M, π.base x = π.base x' ↔ ∃ h : H, (ρ h).hom.base x = x')
    (hsec : ∀ V : X.Opens, Function.Injective (π.app V))
    (hinv : ∀ V : X.Opens, Set.range (π.app V) =
      {s | ∀ h : H, (ρ h).hom.appLE (π ⁻¹ᵁ V) (π ⁻¹ᵁ V) (by rw [← Scheme.Hom.comp_preimage, hπ h]) s = s})
    {M' X' : Scheme.{0}} (πM' : M' ⟶ Spec (CommRingCat.of 𝒪)) (πX' : X' ⟶ Spec (CommRingCat.of 𝒪))
    (gM : M' ⟶ M) (hgM : IsPullback gM πM' πM (Spec.map (CommRingCat.ofHom i)))
    (gX : X' ⟶ X) (hgX : IsPullback gX πX' πX (Spec.map (CommRingCat.ofHom i)))
    (π' : M' ⟶ X') (hπX' : π' ≫ πX' = πM') (hπg : π' ≫ gX = gM ≫ π)
    (ρ' : H →* Aut M') (hover' : ∀ h : H, (ρ' h).hom ≫ πM' = πM') (hρg : ∀ h : H, (ρ' h).hom ≫ gM = gM ≫ (ρ h).hom) :
    ∀ y y' : M', π'.base y = π'.base y' ↔ ∃ h : H, (ρ' h).hom.base y = y' := by

  have hπ' : ∀ h : H, (ρ' h).hom ≫ π' = π' := by
    intro h
    apply hgX.hom_ext
    · rw [Category.assoc, hπg, ← Category.assoc, hρg h, Category.assoc, hπ h]
    · rw [Category.assoc, hπX', hover' h]
  obtain ⟨-, haff', -, -, hinv'⟩ :=
    AlgebraicGeometry.Scheme.quotientInvariants_pullback_of_flat i hi πM πX π hπX ρ hover hπ hint haff hsurj hsec hinv
      πM' πX' gM hgM gX hgX π' hπX' hπg ρ' hover' hρg hπ'
  exact AlgebraicGeometry.Scheme.orbit_iff_of_isAffineHom_of_invariants π' ρ' hπ' haff' hinv'
