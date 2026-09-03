import Mathlib
import P2M.Util
import P2M.Sol.S_Module_exists_forall_notMem_and_linearIndependent_and_smul_mem_span_of_finrank_baseChange_eq

set_option autoImplicit false

universe u v

theorem Module.exists_forall_notMem_and_linearIndependent_and_smul_mem_span_of_finrank_baseChange_eq
    {A : Type u} [CommRing A] [IsDomain A] {P : Type v} [AddCommGroup P] [Module A P] [Module.Finite A P]
    (d : ℕ) (S : Finset (Ideal A)) (hS : ∀ 𝔭 ∈ S, 𝔭.IsMaximal) (hSne : S.Nonempty)
    (hrank : ∀ (K : Type u) [Field K] [Algebra A K], Module.finrank K (TensorProduct A K P) = d) :
    ∃ (f : A) (e : Fin d → P), (∀ 𝔭 ∈ S, f ∉ 𝔭) ∧ LinearIndependent A e ∧
      ∀ p : P, f • p ∈ Submodule.span A (Set.range e) := by p2m_exact_reverting @_root_.P2MW.S_Module_exists_forall_notMem_and_linearIndependent_and_smul_mem_span_of_finrank_baseChange_eq.solution
