import Mathlib
import P2M.Util
import P2M.Sol.S_Ideal_exists_eq_smul_one_tmul_and_one_tmul_eq_zero_of_isLocalization

set_option autoImplicit false

open MvPolynomial TensorProduct

theorem Ideal.exists_eq_smul_one_tmul_and_one_tmul_eq_zero_of_isLocalization
    (R : Type) [CommRing R] {n : ℕ} (M : Submonoid (MvPolynomial (Fin n) R))
    (P : Type) [CommRing P] [Algebra (MvPolynomial (Fin n) R) P] [IsLocalization M P]
    (I J : Ideal (MvPolynomial (Fin n) R)) (𝔞 : Ideal P) (h𝔞 : 𝔞 = I.map (algebraMap (MvPolynomial (Fin n) R) P))
    (K : Type) [CommRing K] [Algebra P K] [Algebra (MvPolynomial (Fin n) R) K]
    [IsScalarTower (MvPolynomial (Fin n) R) P K]
    (hK : Function.Surjective (algebraMap (MvPolynomial (Fin n) R) K))
    (hJK : ∀ j ∈ J, algebraMap (MvPolynomial (Fin n) R) K j = 0) :
    (∀ z : K ⊗[P] ↥𝔞, ∃ (c : K) (a : MvPolynomial (Fin n) R) (ha : a ∈ I),
        z = c • ((1 : K) ⊗ₜ[P] (⟨algebraMap (MvPolynomial (Fin n) R) P a,
          h𝔞 ▸ Ideal.mem_map_of_mem (algebraMap (MvPolynomial (Fin n) R) P) ha⟩ : ↥𝔞))) ∧
    (∀ (a : MvPolynomial (Fin n) R) (ha : a ∈ J * I),
        ((1 : K) ⊗ₜ[P] (⟨algebraMap (MvPolynomial (Fin n) R) P a,
          h𝔞 ▸ Ideal.mem_map_of_mem (algebraMap (MvPolynomial (Fin n) R) P) (Ideal.mul_le_right ha)⟩ : ↥𝔞) : K ⊗[P] ↥𝔞) = 0) := by p2m_exact_reverting @_root_.P2MW.S_Ideal_exists_eq_smul_one_tmul_and_one_tmul_eq_zero_of_isLocalization.solution
