import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_exists_iso_quotient_pullback_of_flat

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.exists_iso_quotient_pullback_of_flat
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
    (hcat : ∀ (T : Scheme.{0}) (f : M ⟶ T), (∀ h : H, (ρ h).hom ≫ f = f) → ∃! f' : X ⟶ T, π ≫ f' = f)

    {M' : Scheme.{0}} (πM' : M' ⟶ Spec (CommRingCat.of 𝒪))
    (gM : M' ⟶ M) (hgM : IsPullback gM πM' πM (Spec.map (CommRingCat.ofHom i)))
    (ρ' : H →* Aut M') (hover' : ∀ h : H, (ρ' h).hom ≫ πM' = πM') (hρg : ∀ h : H, (ρ' h).hom ≫ gM = gM ≫ (ρ h).hom)

    {Y : Scheme.{0}} (πYb : Y ⟶ Spec (CommRingCat.of 𝒪)) (πY : M' ⟶ Y) (hπYb : πY ≫ πYb = πM')
    (hπY : ∀ h : H, (ρ' h).hom ≫ πY = πY)
    (hintY : IsIntegralHom πY) (haffY : IsAffineHom πY) (hsurjY : Function.Surjective πY.base)
    (horbitY : ∀ y y' : M', πY.base y = πY.base y' ↔ ∃ h : H, (ρ' h).hom.base y = y')
    (hsecY : ∀ V : Y.Opens, Function.Injective (πY.app V))
    (hinvY : ∀ V : Y.Opens, Set.range (πY.app V) =
      {s | ∀ h : H, (ρ' h).hom.appLE (πY ⁻¹ᵁ V) (πY ⁻¹ᵁ V) (by rw [← Scheme.Hom.comp_preimage, hπY h]) s = s})
    (hcatY : ∀ (T : Scheme.{0}) (f : M' ⟶ T), (∀ h : H, (ρ' h).hom ≫ f = f) → ∃! f' : Y ⟶ T, πY ≫ f' = f) :
    ∃ e : Y ⟶ pullback πX (Spec.map (CommRingCat.ofHom i)),
      IsIso e ∧ e ≫ pullback.snd πX (Spec.map (CommRingCat.ofHom i)) = πYb ∧
      πY ≫ e = pullback.lift (gM ≫ π) πM' (by rw [Category.assoc, hπX, hgM.w]) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_exists_iso_quotient_pullback_of_flat.solution
