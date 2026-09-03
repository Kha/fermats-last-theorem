import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_forall_isUnit_polynomialEval2_comap_of_residuallyNonconstant

set_option autoImplicit false

open IsLocalRing

theorem ValuationSubring.exists_forall_isUnit_polynomialEval2_comap_of_residuallyNonconstant
    {F : Type} [Field F] (F₀ : Subfield F)
    (halg : ∀ x : F, IsAlgebraic ↥F₀ x)
    (O : ValuationSubring F)
    {A₀ : Type} [CommRing A₀] [IsLocalRing A₀]
    (j : A₀ →+* ↥F₀) (hjO : ∀ a : A₀, ((j a : ↥F₀) : F) ∈ O)

    (hloc : ∀ a : A₀, a ∈ maximalIdeal A₀ → ∃ h : ((j a : ↥F₀) : F) ∈ O, (⟨_, h⟩ : ↥O) ∈ maximalIdeal ↥O)
    (hac : ∀ p : Polynomial A₀, p.Monic → 0 < p.natDegree →
      ∃ a : A₀, ∃ h : ((j (p.eval a) : ↥F₀) : F) ∈ O, (⟨_, h⟩ : ↥O) ∈ maximalIdeal ↥O)

    (A : Subring F) (hAO : ∀ a : F, a ∈ A → a ∈ O) (hjA : ∀ a₀ : A₀, ((j a₀ : ↥F₀) : F) ∈ A)
    (hres : ∀ a : F, a ∈ A → ∃ a₀ : A₀, ∃ h : a - ((j a₀ : ↥F₀) : F) ∈ O, (⟨_, h⟩ : ↥O) ∈ maximalIdeal ↥O)

    (t : F) (ht : t ∈ O) (htu : ∀ a : F, a ∈ A → ∃ h : t - a ∈ O, IsUnit (⟨_, h⟩ : ↥O)) :
    ∃ f : ↥F₀, f ∈ O.comap F₀.subtype ∧ ∀ p : Polynomial A₀, (∃ i, IsUnit (p.coeff i)) →
      ∃ hO : Polynomial.eval₂ j f p ∈ O.comap F₀.subtype, IsUnit (⟨_, hO⟩ : ↥(O.comap F₀.subtype)) := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_forall_isUnit_polynomialEval2_comap_of_residuallyNonconstant.solution
