import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_isRegularLocalRing_of_formallySmooth_of_formallyUnramified_polynomial_of_henselianLocalRing

set_option autoImplicit false

open IsLocalRing

theorem IsLocalRing.isRegularLocalRing_of_formallySmooth_of_formallyUnramified_polynomial_of_henselianLocalRing
    {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [HenselianLocalRing A]
    (ϖ : A) (hϖ : maximalIdeal A = Ideal.span {ϖ})
    {S : Type} [CommRing S] [IsDomain S] [IsLocalRing S]
    (φ : Polynomial A →+* S) (hφs : φ.FormallySmooth) (hφu : φ.FormallyUnramified) (hφf : φ.EssFiniteType)
    (χ₀ : S →+* ResidueField A) (hχ₀ : RingHom.ker χ₀ = maximalIdeal S)
    (hχ₀C : ∀ a : A, χ₀ (φ (Polynomial.C a)) = IsLocalRing.residue A a) (hχ₀t : χ₀ (φ Polynomial.X) = 0) :
    IsRegularLocalRing S ∧ ringKrullDim S ≤ 2 ∧
      maximalIdeal S = Ideal.span {φ (Polynomial.C ϖ), φ Polynomial.X} ∧ Prime (φ (Polynomial.C ϖ)) := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_isRegularLocalRing_of_formallySmooth_of_formallyUnramified_polynomial_of_henselianLocalRing.solution
