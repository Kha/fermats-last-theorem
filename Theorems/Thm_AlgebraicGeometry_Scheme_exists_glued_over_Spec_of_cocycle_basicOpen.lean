import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_exists_glued_over_Spec_of_cocycle_basicOpen

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.exists_glued_over_Spec_of_cocycle_basicOpen
    {S : Type u} [CommRing S] {k : ℕ} (r : Fin k → S) (hr : Ideal.span (Set.range r) = ⊤)
    (X : Fin k → Scheme.{u}) (p : ∀ i, X i ⟶ Spec (CommRingCat.of S))
    (hp : ∀ (i : Fin k) (x : ↥(X i)), (p i).base x ∈ PrimeSpectrum.basicOpen (r i))
    (t : ∀ i j : Fin k, (((p i) ⁻¹ᵁ (PrimeSpectrum.basicOpen (r j)) : (X i).Opens) : Scheme.{u}) ⟶ X j)
    (ht_over : ∀ i j : Fin k, t i j ≫ p j = ((p i) ⁻¹ᵁ (PrimeSpectrum.basicOpen (r j))).ι ≫ p i)
    (ht_self : ∀ i : Fin k, t i i = ((p i) ⁻¹ᵁ (PrimeSpectrum.basicOpen (r i))).ι)
    (hinv : ∀ (i j : Fin k)
      (l : (((p i) ⁻¹ᵁ (PrimeSpectrum.basicOpen (r j)) : (X i).Opens) : Scheme.{u}) ⟶
        (((p j) ⁻¹ᵁ (PrimeSpectrum.basicOpen (r i)) : (X j).Opens) : Scheme.{u})),
      l ≫ ((p j) ⁻¹ᵁ (PrimeSpectrum.basicOpen (r i))).ι = t i j →
        l ≫ t j i = ((p i) ⁻¹ᵁ (PrimeSpectrum.basicOpen (r j))).ι)
    (hcocycle : ∀ (i j l : Fin k)
      (m : (((p i) ⁻¹ᵁ (PrimeSpectrum.basicOpen (r j) ⊓ PrimeSpectrum.basicOpen (r l)) : (X i).Opens) : Scheme.{u}) ⟶
        (((p j) ⁻¹ᵁ (PrimeSpectrum.basicOpen (r l)) : (X j).Opens) : Scheme.{u})),
      m ≫ ((p j) ⁻¹ᵁ (PrimeSpectrum.basicOpen (r l))).ι =
        (X i).homOfLE ((p i).preimage_mono inf_le_left) ≫ t i j →
      m ≫ t j l = (X i).homOfLE ((p i).preimage_mono inf_le_right) ≫ t i l) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ Spec (CommRingCat.of S)) (ι : ∀ i, X i ⟶ Y),
      (∀ i, IsOpenImmersion (ι i)) ∧ (∀ i, ι i ≫ f = p i) ∧
      (∀ i, Set.range (ι i).base = ((f ⁻¹ᵁ (PrimeSpectrum.basicOpen (r i)) : Y.Opens) : Set ↥Y)) ∧
      (∀ i j, t i j ≫ ι j = ((p i) ⁻¹ᵁ (PrimeSpectrum.basicOpen (r j))).ι ≫ ι i) ∧
      (∀ y : ↥Y, ∃ (i : Fin k) (x : ↥(X i)), (ι i).base x = y) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_exists_glued_over_Spec_of_cocycle_basicOpen.solution
