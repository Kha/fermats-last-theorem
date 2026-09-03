import Mathlib
import P2M.Util
import P2M.Sol.S_Module_length_quotient_range_eq_length_dual_quotient_of_isRegular_of_exact

set_option autoImplicit false

universe u

open TensorProduct

theorem Module.length_quotient_range_eq_length_dual_quotient_of_isRegular_of_exact
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] (n : ℕ) (rs : List R)
    (hreg : RingTheory.Sequence.IsRegular R rs) (hlen : rs.length = n + 1)
    (hmax : Ideal.ofList rs = IsLocalRing.maximalIdeal R)
    (K : ℕ → Type u) [∀ i, AddCommGroup (K i)] [∀ i, Module R (K i)]
    [∀ i, Module.Finite R (K i)] [∀ i, Module.Free R (K i)]
    (hbdd : ∀ i, n + 1 < i → Subsingleton (K i))
    (δ : ∀ i, K i →ₗ[R] K (i + 1)) (hdd : ∀ i, δ (i + 1) ∘ₗ δ i = 0)
    (hex0 : ∀ z : K 0, δ 0 z = 0 → z = 0)
    (hex : ∀ i, i < n → ∀ z : K (i + 1), δ (i + 1) z = 0 → z ∈ LinearMap.range (δ i))
    (htors : ∃ N : ℕ, ∀ a ∈ IsLocalRing.maximalIdeal R ^ N, ∀ q : K (n + 1) ⧸ LinearMap.range (δ n), a • q = 0) :
    Module.length R (K (n + 1) ⧸ LinearMap.range (δ n)) =
      Module.length R (Module.Dual R (K 0) ⧸ LinearMap.range (δ 0).dualMap) := by p2m_exact_reverting @_root_.P2MW.S_Module_length_quotient_range_eq_length_dual_quotient_of_isRegular_of_exact.solution
