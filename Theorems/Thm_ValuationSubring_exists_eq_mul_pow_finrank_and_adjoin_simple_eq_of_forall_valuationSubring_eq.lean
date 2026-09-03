import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_eq_mul_pow_finrank_and_adjoin_simple_eq_of_forall_valuationSubring_eq

set_option autoImplicit false

open IsLocalRing
open scoped IntermediateField

theorem ValuationSubring.exists_eq_mul_pow_finrank_and_adjoin_simple_eq_of_forall_valuationSubring_eq
    {L : Type*} [Field L] [CharZero L] (A : ValuationSubring L)
    (C : Subring L) (hC : ∀ c : L, c ∈ C → c ∈ A) [IsDomain ↥C] [IsDiscreteValuationRing ↥C]
    (ϖ : ↥C)
    (hϖ : ∀ d : ↥C, IsLocalRing.residue A ⟨(d : L), hC d d.2⟩ = 0 ↔ ∃ d' : ↥C, d = ϖ * d')
    (hϖ0 : ((ϖ : ↥C) : L) ≠ 0)
    (hκ : ∀ a : ↥A, ∃ c : ↥C, a - ⟨(c : L), hC c c.2⟩ ∈ maximalIdeal ↥A)
    (huniq : ∀ V : ValuationSubring L, (∀ c : L, c ∈ C → c ∈ V) → ((ϖ : ↥C) : L) ∈ V.nonunits → V = A)
    (K₀ : Type*) [Field K₀] [Algebra ↥C K₀] [IsFractionRing ↥C K₀] [Algebra K₀ L] [IsScalarTower ↥C K₀ L]
    (K₁ : IntermediateField K₀ L) [FiniteDimensional K₀ ↥K₁] :
    ∃ ϖ₁ v w : L, ϖ₁ ∈ K₁ ∧ v ∈ K₁ ∧ w ∈ K₁ ∧
      IsIntegral ↥C ϖ₁ ∧ IsIntegral ↥C v ∧ IsIntegral ↥C w ∧ v * w = 1 ∧
      ((ϖ : ↥C) : L) = v * ϖ₁ ^ Module.finrank K₀ ↥K₁ ∧
      K₀⟮ϖ₁⟯ = K₁ := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_eq_mul_pow_finrank_and_adjoin_simple_eq_of_forall_valuationSubring_eq.solution
