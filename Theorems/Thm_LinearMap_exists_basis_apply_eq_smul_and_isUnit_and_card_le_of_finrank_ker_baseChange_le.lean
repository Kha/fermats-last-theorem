import Mathlib
import P2M.Util
import P2M.Sol.S_LinearMap_exists_basis_apply_eq_smul_and_isUnit_and_card_le_of_finrank_ker_baseChange_le

set_option autoImplicit false

open scoped TensorProduct

theorem LinearMap.exists_basis_apply_eq_smul_and_isUnit_and_card_le_of_finrank_ker_baseChange_le
    (R : Type) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [IsLocalRing R]
    (M : Type) [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
    (f : M →ₗ[R] M) (hf : Function.Injective f) (r : ℕ)
    (hker : Module.finrank (IsLocalRing.ResidueField R)
        (LinearMap.ker (f.baseChange (IsLocalRing.ResidueField R))) ≤ r) :
    ∃ (n : ℕ) (b b' : Module.Basis (Fin n) R M) (a : Fin n → R) (s : Finset (Fin n)),
      (∀ i, f (b i) = a i • b' i) ∧ (∀ i ∉ s, IsUnit (a i)) ∧ s.card ≤ r := by p2m_exact_reverting @_root_.P2MW.S_LinearMap_exists_basis_apply_eq_smul_and_isUnit_and_card_le_of_finrank_ker_baseChange_le.solution
