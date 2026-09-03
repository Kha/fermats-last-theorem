import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_card_algHom_le_finsum_finrank_quotient

set_option autoImplicit false

universe u v

open IsLocalRing

theorem Algebra.card_algHom_le_finsum_finrank_quotient
    {Ô : Type u} [CommRing Ô] [IsDomain Ô] [IsDiscreteValuationRing Ô]
    (ϖ : Ô) (hϖ0 : ϖ ≠ 0)
    (S : Type u) [CommRing S] [Algebra Ô S] [Module.Finite Ô S]
    (C : Type v) [Field C] [Algebra Ô C] (hinj : Function.Injective (algebraMap Ô C))
    (Φ : Finset (S →ₐ[Ô] C)) :
    (Φ.card : ℕ∞) ≤
      ∑ᶠ (𝔓 : PrimeSpectrum S) (_ : 𝔓.asIdeal ∈ minimalPrimes S ∧ algebraMap Ô S ϖ ∉ 𝔓.asIdeal),
        (Module.finrank Ô (S ⧸ 𝔓.asIdeal) : ℕ∞) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_card_algHom_le_finsum_finrank_quotient.solution
