import Mathlib
import P2M.Util
import P2M.Sol.S_Module_Flat_ker_le_range_of_forall_isMaximal_ker_baseChange_quotient_le_range

set_option autoImplicit false

universe u

open TensorProduct

theorem Module.Flat.ker_le_range_of_forall_isMaximal_ker_baseChange_quotient_le_range
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (C : ℕ → Type u) [∀ i, AddCommGroup (C i)] [∀ i, Module R (C i)] [∀ i, Module.Flat R (C i)]
    (d : ∀ i, C i →ₗ[R] C (i + 1)) (hdd : ∀ i, d (i + 1) ∘ₗ d i = 0)
    (n : ℕ) (hbd : ∀ i, n ≤ i → Subsingleton (C i))
    (hfin : ∀ i, Module.Finite R
      (LinearMap.ker (d (i + 1)) ⧸ (LinearMap.range (d i)).comap (LinearMap.ker (d (i + 1))).subtype))
    (hfib : ∀ (𝔪 : Ideal R) [𝔪.IsMaximal] (i : ℕ),
      LinearMap.ker ((d (i + 1)).baseChange (R ⧸ 𝔪)) ≤ LinearMap.range ((d i).baseChange (R ⧸ 𝔪))) :
    ∀ i : ℕ, LinearMap.ker (d (i + 1)) ≤ LinearMap.range (d i) := by p2m_exact_reverting @_root_.P2MW.S_Module_Flat_ker_le_range_of_forall_isMaximal_ker_baseChange_quotient_le_range.solution
