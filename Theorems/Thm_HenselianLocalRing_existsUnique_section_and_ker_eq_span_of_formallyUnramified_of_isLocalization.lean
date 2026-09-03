import Mathlib
import P2M.Util
import P2M.Sol.S_HenselianLocalRing_existsUnique_section_and_ker_eq_span_of_formallyUnramified_of_isLocalization

set_option autoImplicit false

open IsLocalRing

universe u

theorem HenselianLocalRing.existsUnique_section_and_ker_eq_span_of_formallyUnramified_of_isLocalization
    {A : Type u} [CommRing A] [HenselianLocalRing A]
    {S : Type u} [CommRing S] [IsLocalRing S]
    (φ : Polynomial A →+* S) (hφs : φ.FormallySmooth) (hφu : φ.FormallyUnramified)
    (P : Type u) [CommRing P] [Algebra A P] [Algebra.FinitePresentation A P] (M : Submonoid P)
    [Algebra P S] [IsLocalization M S]
    (hPS : ∀ a : A, algebraMap P S (algebraMap A P a) = φ (Polynomial.C a))
    (χ₀ : S →+* ResidueField A) (hχ₀ : RingHom.ker χ₀ = maximalIdeal S)
    (hχ₀C : ∀ a : A, χ₀ (φ (Polynomial.C a)) = IsLocalRing.residue A a) (hχ₀t : χ₀ (φ Polynomial.X) = 0) :
    (∀ c : A, IsLocalRing.residue A c = 0 →
      ∃! χ : S →+* A, (∀ a : A, χ (φ (Polynomial.C a)) = a) ∧
        (∀ f : S, IsLocalRing.residue A (χ f) = χ₀ f) ∧ χ (φ Polynomial.X) = c) ∧
    (∀ χ : S →+* A, (∀ a : A, χ (φ (Polynomial.C a)) = a) → (∀ f : S, IsLocalRing.residue A (χ f) = χ₀ f) →
      RingHom.ker χ = Ideal.span {φ Polynomial.X - φ (Polynomial.C (χ (φ Polynomial.X)))}) := by p2m_exact_reverting @_root_.P2MW.S_HenselianLocalRing_existsUnique_section_and_ker_eq_span_of_formallyUnramified_of_isLocalization.solution
