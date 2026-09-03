import Mathlib
import P2M.Util
import P2M.Sol.S_IsDiscreteValuationRing_exists_cyclotomic_dvr_of_maximalIdeal_eq_span_prime

set_option autoImplicit false

open IsLocalRing Polynomial

theorem IsDiscreteValuationRing.exists_cyclotomic_dvr_of_maximalIdeal_eq_span_prime
    (q : ℕ) [Fact q.Prime]
    (W₀ : Type) [CommRing W₀] [IsDomain W₀] [IsDiscreteValuationRing W₀]
    [IsAdicComplete (IsLocalRing.maximalIdeal W₀) W₀] (hW₀ : IsLocalRing.maximalIdeal W₀ = Ideal.span {(q : W₀)})
    (k : Type) [Field k] [CharP k q]
    (res₀ : W₀ →+* k) (hres₀ : Function.Surjective res₀) (hker₀ : RingHom.ker res₀ = IsLocalRing.maximalIdeal W₀) :
    ∃ (𝒪 : Type) (_ : CommRing 𝒪) (_ : IsDomain 𝒪) (_ : IsDiscreteValuationRing 𝒪) (_ : Algebra W₀ 𝒪)
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪) (ζ : 𝒪) (res : 𝒪 →+* k),
      (∑ i ∈ Finset.range q, ζ ^ i) = 0 ∧
      IsLocalRing.maximalIdeal 𝒪 = Ideal.span {ζ - 1} ∧
      Function.Surjective res ∧ RingHom.ker res = IsLocalRing.maximalIdeal 𝒪 ∧
      (∀ w : W₀, res (algebraMap W₀ 𝒪 w) = res₀ w) ∧
      (∀ (S : Type) [CommRing S] [Algebra W₀ S] (z : S), (∑ i ∈ Finset.range q, z ^ i) = 0 →
        ∃! f : 𝒪 →ₐ[W₀] S, f ζ = z) := by p2m_exact_reverting @_root_.P2MW.S_IsDiscreteValuationRing_exists_cyclotomic_dvr_of_maximalIdeal_eq_span_prime.solution
