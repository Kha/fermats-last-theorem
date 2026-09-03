import Mathlib
import P2M.Util
import P2M.Sol.S_LinearMap_exists_apply_basis_eq_smul_of_mul_eq_pow_mul_of_toMatrix_sub_one_mem

set_option autoImplicit false

universe u v
theorem LinearMap.exists_apply_basis_eq_smul_of_mul_eq_pow_mul_of_toMatrix_sub_one_mem {R : Type u} [CommRing R] [IsLocalRing R]
    (hH : ∀ x : R, (∀ n : ℕ, x ∈ IsLocalRing.maximalIdeal R ^ n) → x = 0)
    {V : Type v} [AddCommGroup V] [Module R V] (b : Module.Basis (Fin 2) R V) (Φ N : Module.End R V)
    {a d : R} {q : ℕ} (hΦ0 : Φ (b 0) = a • b 0) (hΦ1 : Φ (b 1) = d • b 1)
    (had : IsUnit (a - (q : R) * d)) (hda : IsUnit (d - (q : R) * a))
    (hN : ∀ i j, LinearMap.toMatrix b b N i j - (1 : Matrix (Fin 2) (Fin 2) R) i j ∈ IsLocalRing.maximalIdeal R)
    (hrel : Φ * N = N ^ q * Φ) :
    ∃ x y : R, IsUnit x ∧ IsUnit y ∧ N (b 0) = x • b 0 ∧ N (b 1) = y • b 1 := by p2m_exact_reverting @_root_.P2MW.S_LinearMap_exists_apply_basis_eq_smul_of_mul_eq_pow_mul_of_toMatrix_sub_one_mem.solution
