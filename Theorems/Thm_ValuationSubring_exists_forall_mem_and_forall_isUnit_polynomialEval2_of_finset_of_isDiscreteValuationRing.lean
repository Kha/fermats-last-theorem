import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_forall_mem_and_forall_isUnit_polynomialEval2_of_finset_of_isDiscreteValuationRing

set_option autoImplicit false

open IsLocalRing

theorem ValuationSubring.exists_forall_mem_and_forall_isUnit_polynomialEval2_of_finset_of_isDiscreteValuationRing
    {A₀ : Type} [CommRing A₀] {F₀ : Type} [Field F₀] (j₀ : A₀ →+* F₀)
    (V : Finset (ValuationSubring F₀))
    (hdvr : ∀ O ∈ V, IsDiscreteValuationRing ↥O)
    (hgeo : ∀ O ∈ V, ∃ f : F₀, f ∈ O ∧ ∀ p : Polynomial A₀, (∃ i, IsUnit (p.coeff i)) →
      ∃ hO : Polynomial.eval₂ j₀ f p ∈ O, IsUnit (⟨_, hO⟩ : ↥O)) :
    ∃ f : F₀, ∀ O ∈ V, f ∈ O ∧ ∀ p : Polynomial A₀, (∃ i, IsUnit (p.coeff i)) →
      ∃ hO : Polynomial.eval₂ j₀ f p ∈ O, IsUnit (⟨_, hO⟩ : ↥O) := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_forall_mem_and_forall_isUnit_polynomialEval2_of_finset_of_isDiscreteValuationRing.solution
