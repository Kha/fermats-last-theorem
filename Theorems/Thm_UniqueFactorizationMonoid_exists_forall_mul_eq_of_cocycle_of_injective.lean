import Mathlib
import P2M.Util
import P2M.Sol.S_UniqueFactorizationMonoid_exists_forall_mul_eq_of_cocycle_of_injective

set_option autoImplicit false

theorem UniqueFactorizationMonoid.exists_forall_mul_eq_of_cocycle_of_injective
    {B : Type*} [CommRing B] [IsDomain B] [UniqueFactorizationMonoid B]
    {K : Type*} [Field K] (φ : B →+* K) (hφ : Function.Injective φ)
    {ι : Type*} (b : ι → B) (u : ι → ι → K)
    (hreg : ∀ i j, b i ≠ 0 → b j ≠ 0 → ∃ (n : ℕ) (x : B), u i j * φ (b i * b j) ^ n = φ x)
    (hrefl : ∀ i, b i ≠ 0 → u i i = 1)
    (hcocycle : ∀ i j k, b i ≠ 0 → b j ≠ 0 → b k ≠ 0 → u i j * u j k = u i k) :
    ∃ h : ι → K, (∀ i, b i ≠ 0 →
        h i ≠ 0 ∧ (∃ (n : ℕ) (x : B), h i * φ (b i) ^ n = φ x) ∧
          (∃ (n : ℕ) (y : B), (h i)⁻¹ * φ (b i) ^ n = φ y)) ∧
      ∀ i j, b i ≠ 0 → b j ≠ 0 → u i j * h j = h i := by p2m_exact_reverting @_root_.P2MW.S_UniqueFactorizationMonoid_exists_forall_mul_eq_of_cocycle_of_injective.solution
