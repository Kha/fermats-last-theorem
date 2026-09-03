import Mathlib
import Definitions.Def_ValuationSubring_CompletionRatClosure
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_exists_liesOverPrime_ringEquiv_ratClosure_range_iff_of_isAdicComplete_of_natCard_quotient_eq

set_option autoImplicit false

p2m_open "IsDedekindDomain NumberField ValuationSubring~exists_ringEquiv_adicCompletion_ratClosure_of_liesOverPrime"

theorem CerednikDrinfeld.exists_liesOverPrime_ringEquiv_ratClosure_range_iff_of_isAdicComplete_of_natCard_quotient_eq
    (r : ℕ) [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (K₀ : Type) [Field K₀] [CharZero K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀] :
    ∃ (A : ValuationSubring (AlgebraicClosure ℚ)) (_ : A.LiesOverPrime r) (e : K₀ ≃+* ↥(ratClosure A)),
      ∀ x : ↥(ratClosure A), x ∈ Set.range (e.toRingHom.comp (algebraMap 𝒪 K₀)) ↔
        Valued.v (algebraMap ↥(ratClosure A) A.valuation.Completion x) ≤ 1 := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_exists_liesOverPrime_ringEquiv_ratClosure_range_iff_of_isAdicComplete_of_natCard_quotient_eq.solution
