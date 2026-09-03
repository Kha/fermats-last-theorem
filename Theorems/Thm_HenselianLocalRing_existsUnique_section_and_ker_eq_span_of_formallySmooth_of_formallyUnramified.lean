import Mathlib
import P2M.Util
import P2M.Sol.S_HenselianLocalRing_existsUnique_section_and_ker_eq_span_of_formallySmooth_of_formallyUnramified

set_option autoImplicit false

open IsLocalRing

theorem HenselianLocalRing.existsUnique_section_and_ker_eq_span_of_formallySmooth_of_formallyUnramified
    {A : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [HenselianLocalRing A]
    {S : Type} [CommRing S] [IsLocalRing S]
    (φ : Polynomial A →+* S) (hφs : φ.FormallySmooth) (hφu : φ.FormallyUnramified) (hφf : φ.EssFiniteType)
    (χ₀ : S →+* ResidueField A) (hχ₀ : RingHom.ker χ₀ = maximalIdeal S)
    (hχ₀C : ∀ a : A, χ₀ (φ (Polynomial.C a)) = IsLocalRing.residue A a) (hχ₀t : χ₀ (φ Polynomial.X) = 0) :
    (∀ c : A, IsLocalRing.residue A c = 0 →
      ∃! χ : S →+* A, (∀ a : A, χ (φ (Polynomial.C a)) = a) ∧
        (∀ f : S, IsLocalRing.residue A (χ f) = χ₀ f) ∧ χ (φ Polynomial.X) = c) ∧
    (∀ χ : S →+* A, (∀ a : A, χ (φ (Polynomial.C a)) = a) → (∀ f : S, IsLocalRing.residue A (χ f) = χ₀ f) →
      RingHom.ker χ = Ideal.span {φ Polynomial.X - φ (Polynomial.C (χ (φ Polynomial.X)))}) := by p2m_exact_reverting @_root_.P2MW.S_HenselianLocalRing_existsUnique_section_and_ker_eq_span_of_formallySmooth_of_formallyUnramified.solution
