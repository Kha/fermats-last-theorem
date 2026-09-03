import Mathlib
import P2M.Util
import P2M.Sol.S_exists_forall_pow_smul_eq_smul_of_forall_exists_smul_eq_smul

theorem exists_forall_pow_smul_eq_smul_of_forall_exists_smul_eq_smul
    {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (ϖ : R) (hϖ : Irreducible ϖ)
    {A : Type} [CommRing A] [Algebra R A]
    {M : Type} [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
    [Module.Finite R M]
    (g : M) (hcyc : ∀ x : M, ∃ d : R, d ≠ 0 ∧ ∃ t : A, d • x = t • g) :
    ∃ a : ℕ, ∀ x : M, ∃ t : A, ϖ ^ a • x = t • g := by p2m_exact_reverting @_root_.P2MW.S_exists_forall_pow_smul_eq_smul_of_forall_exists_smul_eq_smul.solution
