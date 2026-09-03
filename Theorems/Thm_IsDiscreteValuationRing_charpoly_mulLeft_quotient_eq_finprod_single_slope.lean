import Mathlib
import P2M.Util
import P2M.Sol.S_IsDiscreteValuationRing_charpoly_mulLeft_quotient_eq_finprod_single_slope

set_option autoImplicit false

universe u

open IsLocalRing Polynomial
open scoped TensorProduct

theorem IsDiscreteValuationRing.charpoly_mulLeft_quotient_eq_finprod_single_slope
    {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
    (R : Type u) [CommRing R] [Algebra W R] (x u : R)
    [Module.Free W (R ⧸ Ideal.span {x})] [Module.Finite W (R ⧸ Ideal.span {x})]
    (hff : ∀ P : PrimeSpectrum R, Ideal.span {x} ≤ P.asIdeal →
      Disjoint (↑(Algebra.algebraMapSubmonoid R (nonZeroDivisors W)) : Set R) ↑P.asIdeal →
        Module.Finite W (R ⧸ P.asIdeal) ∧ Module.Free W (R ⧸ P.asIdeal)) :
    ∃ χP : PrimeSpectrum R → Polynomial W,
      (∀ P : PrimeSpectrum R, Ideal.span {x} ≤ P.asIdeal →
        Disjoint (↑(Algebra.algebraMapSubmonoid R (nonZeroDivisors W)) : Set R) ↑P.asIdeal →
          (χP P).Monic ∧ (χP P).natDegree = (Module.finrank W (R ⧸ P.asIdeal) * (Module.length (Localization.AtPrime P.asIdeal) (LocalizedModule P.asIdeal.primeCompl (R ⧸ Ideal.span {x}))).toNat) ∧
          (∀ i : ℕ, i ≤ (Module.finrank W (R ⧸ P.asIdeal) * (Module.length (Localization.AtPrime P.asIdeal) (LocalizedModule P.asIdeal.primeCompl (R ⧸ Ideal.span {x}))).toNat) →
            (((Module.finrank W (R ⧸ P.asIdeal) * (Module.length (Localization.AtPrime P.asIdeal) (LocalizedModule P.asIdeal.primeCompl (R ⧸ Ideal.span {x}))).toNat) - i : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal W (Algebra.norm W (Ideal.Quotient.mk P.asIdeal u)) ≤
              (Module.finrank W (R ⧸ P.asIdeal) : ℕ∞) * IsDiscreteValuationRing.addVal W ((χP P).coeff i)) ∧
          (((Module.finrank W (R ⧸ P.asIdeal) * (Module.length (Localization.AtPrime P.asIdeal) (LocalizedModule P.asIdeal.primeCompl (R ⧸ Ideal.span {x}))).toNat) : ℕ∞) * IsDiscreteValuationRing.addVal W (Algebra.norm W (Ideal.Quotient.mk P.asIdeal u)) =
            (Module.finrank W (R ⧸ P.asIdeal) : ℕ∞) * IsDiscreteValuationRing.addVal W ((χP P).coeff 0))) ∧
      (LinearMap.mulLeft W (Ideal.Quotient.mk (Ideal.span {x}) u)).charpoly =
        ∏ᶠ (P : PrimeSpectrum R) (_ : P ∈ {P : PrimeSpectrum R | Ideal.span {x} ≤ P.asIdeal ∧
            Disjoint (↑(Algebra.algebraMapSubmonoid R (nonZeroDivisors W)) : Set R) ↑P.asIdeal}), χP P ∧
      Module.finrank W (R ⧸ Ideal.span {x}) =
        ∑ᶠ (P : PrimeSpectrum R) (_ : P ∈ {P : PrimeSpectrum R | Ideal.span {x} ≤ P.asIdeal ∧
            Disjoint (↑(Algebra.algebraMapSubmonoid R (nonZeroDivisors W)) : Set R) ↑P.asIdeal}),
          Module.finrank W (R ⧸ P.asIdeal) * (Module.length (Localization.AtPrime P.asIdeal) (LocalizedModule P.asIdeal.primeCompl (R ⧸ Ideal.span {x}))).toNat := by p2m_exact_reverting @_root_.P2MW.S_IsDiscreteValuationRing_charpoly_mulLeft_quotient_eq_finprod_single_slope.solution
