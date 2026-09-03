import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_finset_forall_exists_mem_span_mul_eq_of_intermediateField_le

set_option autoImplicit false

theorem ValuationSubring.exists_finset_forall_exists_mem_span_mul_eq_of_intermediateField_le
    {k L : Type*} [Field k] [Field L] [Algebra k L] [CharZero k] (A : ValuationSubring L)
    (K₀ K' : IntermediateField k L) [FiniteDimensional k ↥K₀] [FiniteDimensional k ↥K'] (hK : K₀ ≤ K')
    (C : Subring L) (hCK₀ : ∀ c : L, c ∈ C ↔ c ∈ A ∧ c ∈ K₀) [IsDomain ↥C] [IsDiscreteValuationRing ↥C]
    (C' : Subring L) (hC'K' : ∀ c : L, c ∈ C' ↔ c ∈ A ∧ c ∈ K')
    (t : L) (htC' : t ∈ C') (htinv : t⁻¹ ∉ C') :
    ∃ G : Finset L, (↑G ⊆ (C' : Set L)) ∧
      ∀ c : L, c ∈ C' → ∃ y z : L, y ∈ Submodule.span ↥C (G : Set L) ∧ z ∈ Submodule.span ↥C (G : Set L) ∧
        z ∈ C' ∧ z⁻¹ ∈ C' ∧ z ≠ 0 ∧ c * z = y := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_finset_forall_exists_mem_span_mul_eq_of_intermediateField_le.solution
