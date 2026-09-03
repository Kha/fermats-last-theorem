import Mathlib
import P2M.Util
import P2M.Sol.S_Ideal_exists_ne_zero_and_forall_isMaximal_radical_map_isPrime

set_option autoImplicit false

universe u v w

theorem Ideal.exists_ne_zero_and_forall_isMaximal_radical_map_isPrime
    (k : Type u) [Field k] {R : Type v} {C : Type w} [CommRing R] [IsDomain R] [Algebra k R]
    [Algebra.FiniteType k R] [CommRing C] [IsDomain C] [Algebra k C] [Algebra R C]
    [IsScalarTower k R C] [Algebra.FiniteType R C] [FaithfulSMul R C]
    (hgi : ∀ θ : FractionRing C,
      IsSeparable (IntermediateField.adjoin k (Set.range (algebraMap R (FractionRing C)))) θ →
      θ ∈ IntermediateField.adjoin k (Set.range (algebraMap R (FractionRing C)))) :
    ∃ r : R, r ≠ 0 ∧ ∀ n : Ideal R, n.IsMaximal → r ∉ n →
      n.map (algebraMap R C) = ⊤ ∨ (n.map (algebraMap R C)).radical.IsPrime := by p2m_exact_reverting @_root_.P2MW.S_Ideal_exists_ne_zero_and_forall_isMaximal_radical_map_isPrime.solution
