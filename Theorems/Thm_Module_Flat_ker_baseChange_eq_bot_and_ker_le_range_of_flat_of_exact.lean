import Mathlib
import P2M.Util
import P2M.Sol.S_Module_Flat_ker_baseChange_eq_bot_and_ker_le_range_of_flat_of_exact

set_option autoImplicit false

universe u

open TensorProduct

theorem Module.Flat.ker_baseChange_eq_bot_and_ker_le_range_of_flat_of_exact
    {R : Type u} [CommRing R] (C : ℕ → Type u) [∀ i, AddCommGroup (C i)] [∀ i, Module R (C i)]
    [∀ i, Module.Flat R (C i)] (d : ∀ i, C i →ₗ[R] C (i + 1))
    (hdd : ∀ i, d (i + 1) ∘ₗ d i = 0) (n : ℕ) (hbd : ∀ i, n ≤ i → Subsingleton (C i))
    (h0 : LinearMap.ker (d 0) = ⊥) (hex : ∀ i, LinearMap.ker (d (i + 1)) ≤ LinearMap.range (d i))
    (A : Type u) [CommRing A] [Algebra R A] :
    LinearMap.ker ((d 0).baseChange A) = ⊥ ∧
      ∀ i, LinearMap.ker ((d (i + 1)).baseChange A) ≤ LinearMap.range ((d i).baseChange A) := by p2m_exact_reverting @_root_.P2MW.S_Module_Flat_ker_baseChange_eq_bot_and_ker_le_range_of_flat_of_exact.solution
