import Mathlib
import P2M.Util
import P2M.Sol.S_Module_exists_forall_alternatingSum_finrank_cohomology_baseChange_eq_of_flat_complex_of_isLocalRing

set_option autoImplicit false

universe u

open TensorProduct

theorem Module.exists_forall_alternatingSum_finrank_cohomology_baseChange_eq_of_flat_complex_of_isLocalRing
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (C : ℕ → Type u) [∀ i, AddCommGroup (C i)] [∀ i, Module R (C i)] [∀ i, Module.Flat R (C i)]
    (d : ∀ i, C i →ₗ[R] C (i + 1)) (hdd : ∀ i, d (i + 1) ∘ₗ d i = 0)
    (n : ℕ) (hbdd : ∀ i, n < i → Subsingleton (C i))
    (hfin0 : Module.Finite R (LinearMap.ker (d 0)))
    (hfin : ∀ i, Module.Finite R
      (LinearMap.ker (d (i + 1)) ⧸ (LinearMap.range (d i)).comap (LinearMap.ker (d (i + 1))).subtype)) :
    ∃ χ₀ : ℤ, ∀ (A : Type u) [Field A] [Algebra R A]
      (H0 : Type u) [AddCommGroup H0] [Module A H0] (_e₀ : H0 ≃ₗ[A] LinearMap.ker ((d 0).baseChange A))
      (H : ℕ → Type u) [∀ i, AddCommGroup (H i)] [∀ i, Module A (H i)]
      (φ : ∀ i, LinearMap.ker ((d (i + 1)).baseChange A) →ₗ[A] H i)
      (_hφ : ∀ i, Function.Surjective (φ i))
      (_hφker : ∀ i, LinearMap.ker (φ i) =
        (LinearMap.range ((d i).baseChange A)).comap (LinearMap.ker ((d (i + 1)).baseChange A)).subtype),
      (Module.finrank A H0 : ℤ) + ∑ i ∈ Finset.range n, (-1 : ℤ) ^ (i + 1) * (Module.finrank A (H i) : ℤ) = χ₀ := by p2m_exact_reverting @_root_.P2MW.S_Module_exists_forall_alternatingSum_finrank_cohomology_baseChange_eq_of_flat_complex_of_isLocalRing.solution
