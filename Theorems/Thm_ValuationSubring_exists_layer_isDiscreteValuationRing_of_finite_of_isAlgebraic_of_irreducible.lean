import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_layer_isDiscreteValuationRing_of_finite_of_isAlgebraic_of_irreducible

set_option autoImplicit false

open IsLocalRing

theorem ValuationSubring.exists_layer_isDiscreteValuationRing_of_finite_of_isAlgebraic_of_irreducible
    {L : Type} [Field L] [CharZero L] (A : ValuationSubring L)
    (C' : Subring L) (hC'A : ∀ c : L, c ∈ C' → c ∈ A) [IsDomain ↥C'] [IsDiscreteValuationRing ↥C'] (ϖ' : ↥C') (hϖ'irr : Irreducible ϖ')
    (hϖ' : ∀ d : ↥C', IsLocalRing.residue ↥A ⟨(d : L), hC'A d d.2⟩ = 0 ↔ ∃ d' : ↥C', d = ϖ' * d')
    (halg : ∀ a : L, a ∈ A → IsAlgebraic ↥C' a)
    (S : Finset L) (hS : ∀ s ∈ S, s ∈ A) :
    ∃ (C'' : Subring L) (_ : IsDomain ↥C'') (_ : IsDiscreteValuationRing ↥C'') (ϖ'' : ↥C'') (e : ℕ) (R : Subring L)
      (hC'C'' : C' ≤ C'') (hC'R : C' ≤ R) (hC''A : ∀ c : L, c ∈ C'' → c ∈ A),
      (∀ s ∈ S, s ∈ C'') ∧

      (∀ c : L, c ∈ C'' ↔ c ∈ A ∧ c ∈ Subfield.closure ((C' : Set L) ∪ ↑S)) ∧

      Irreducible ϖ'' ∧
      (∀ d : ↥C'', IsLocalRing.residue ↥A ⟨(d : L), hC''A d d.2⟩ = 0 ↔ ∃ d' : ↥C'', d = ϖ'' * d') ∧

      1 ≤ e ∧ (∃ v : L, v ∈ C'' ∧ v⁻¹ ∈ C'' ∧ ((ϖ' : ↥C') : L) = v * ((ϖ'' : ↥C'') : L) ^ e) ∧

      R ≤ C'' ∧ (letI : Algebra ↥C' ↥R := (Subring.inclusion hC'R).toAlgebra; Module.Finite ↥C' ↥R) ∧
      (∀ c : L, c ∈ C'' → ∃ r s : L, r ∈ R ∧ s ∈ R ∧ s ≠ 0 ∧ s⁻¹ ∈ C'' ∧ c * s = r) := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_layer_isDiscreteValuationRing_of_finite_of_isAlgebraic_of_irreducible.solution
