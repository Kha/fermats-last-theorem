import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_card_algHom_le_finsum_finrank_quotient_of_valuation_pow_eq

set_option autoImplicit false

universe u v w

open IsLocalRing

theorem Algebra.card_algHom_le_finsum_finrank_quotient_of_valuation_pow_eq
    {Ô : Type u} [CommRing Ô] [IsDomain Ô] [IsDiscreteValuationRing Ô] [IsAdicComplete (maximalIdeal Ô) Ô]
    (ϖ : Ô) (hϖ : Irreducible ϖ)
    (S : Type u) [CommRing S] [Algebra Ô S] [Module.Finite Ô S] (x : S)
    (C : Type v) [Field C] [Algebra Ô C]
    {Γ₀ : Type w} [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation C Γ₀)
    (hv : ∀ a : Ô, v (algebraMap Ô C a) < 1 ↔ a ∈ maximalIdeal Ô)
    (hv0 : ∀ a : Ô, v (algebraMap Ô C a) = 0 → a = 0)
    (r : ℕ) (hr : 1 ≤ r) (p : ℕ)
    (Φ : Finset (S →ₐ[Ô] C)) (hΦ : ∀ φ ∈ Φ, v (φ x) ^ r = v (algebraMap Ô C ϖ) ^ p) :
    (Φ.card : ℕ∞) ≤
      ∑ᶠ (𝔓 : PrimeSpectrum S) (_ : 𝔓.asIdeal ∈ minimalPrimes S ∧ algebraMap Ô S ϖ ∉ 𝔓.asIdeal ∧
          (r : ℕ∞) * Module.length Ô ((S ⧸ 𝔓.asIdeal) ⧸ Ideal.span {Ideal.Quotient.mk 𝔓.asIdeal x}) =
            ((p * Module.finrank Ô (S ⧸ 𝔓.asIdeal) : ℕ) : ℕ∞)),
        (Module.finrank Ô (S ⧸ 𝔓.asIdeal) : ℕ∞) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_card_algHom_le_finsum_finrank_quotient_of_valuation_pow_eq.solution
