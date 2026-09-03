import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_not_mem_and_inv_not_mem_of_dominates_of_residuallyAlgebraic_of_forall_isUnit_polynomialEval2

set_option autoImplicit false

open IsLocalRing

theorem ValuationSubring.not_mem_and_inv_not_mem_of_dominates_of_residuallyAlgebraic_of_forall_isUnit_polynomialEval2
    {A₀ : Type} [CommRing A₀] {F : Type} [Field F] (j₀ : A₀ →+* F)
    (O : ValuationSubring F) (S : Subring F)
    (hSO : S ≤ O.toSubring)

    (hdom : ∀ s ∈ S, s⁻¹ ∉ S → s ∈ O.nonunits)

    (halg : ∀ s ∈ S, ∃ p : Polynomial A₀, (∃ i, IsUnit (p.coeff i)) ∧
      (Polynomial.eval₂ j₀ s p = 0 ∨ (Polynomial.eval₂ j₀ s p ∈ S ∧ (Polynomial.eval₂ j₀ s p)⁻¹ ∉ S)))
    (g : F)
    (hgeo : ∀ p : Polynomial A₀, (∃ i, IsUnit (p.coeff i)) →
      ∃ hO : Polynomial.eval₂ j₀ g p ∈ O, IsUnit (⟨_, hO⟩ : ↥O)) :
    g ∉ S ∧ g⁻¹ ∉ S := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_not_mem_and_inv_not_mem_of_dominates_of_residuallyAlgebraic_of_forall_isUnit_polynomialEval2.solution
