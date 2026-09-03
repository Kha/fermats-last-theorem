import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_heightOneSpectrum_asIdeal_eq_and_eq_valuationSubring_of_forall_mem_iff_valuation_lt_one

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem ValuationSubring.exists_heightOneSpectrum_asIdeal_eq_and_eq_valuationSubring_of_forall_mem_iff_valuation_lt_one
    (L : Type) [Field L] [NumberField L] (A : ValuationSubring L) (Q : Ideal (𝓞 L)) [Q.IsMaximal]
    (hA : ∀ x : 𝓞 L, A.valuation (algebraMap (𝓞 L) L x) ≤ 1)
    (hQ : ∀ x : 𝓞 L, x ∈ Q ↔ A.valuation (algebraMap (𝓞 L) L x) < 1) :
    ∃ w : HeightOneSpectrum (𝓞 L), w.asIdeal = Q ∧ A = (w.valuation L).valuationSubring := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_heightOneSpectrum_asIdeal_eq_and_eq_valuationSubring_of_forall_mem_iff_valuation_lt_one.solution
