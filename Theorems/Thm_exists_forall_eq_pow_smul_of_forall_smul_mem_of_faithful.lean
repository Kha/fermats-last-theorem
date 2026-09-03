import Mathlib
import P2M.Util
import P2M.Sol.S_exists_forall_eq_pow_smul_of_forall_smul_mem_of_faithful

theorem exists_forall_eq_pow_smul_of_forall_smul_mem_of_faithful
    {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (ϖ : R) (hϖ : Irreducible ϖ)
    {A : Type} [CommRing A] [Algebra R A]
    {M : Type} [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
    [Module.Finite R M] [NoZeroSMulDivisors R M]
    (hfaith : ∀ t : A, (∀ x : M, t • x = 0) → t = 0) :
    ∃ b : ℕ, ∀ (m : ℕ) (t : A), (∀ x : M, ∃ y : M, t • x = ϖ ^ (m + b) • y) →
      ∃ t' : A, t = ϖ ^ m • t' := by p2m_exact_reverting @_root_.P2MW.S_exists_forall_eq_pow_smul_of_forall_smul_mem_of_faithful.solution
