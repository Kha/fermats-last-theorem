import Mathlib
import P2M.Util
import P2M.Sol.S_PadicInt_ncard_setOf_forall_apply_eq_nsmul_sq_eq_card_range_of_forall_sub_mem_iInf_ker

set_option autoImplicit false

theorem PadicInt.ncard_setOf_forall_apply_eq_nsmul_sq_eq_card_range_of_forall_sub_mem_iInf_ker
    (p : ℕ) [Fact p.Prime] {ι : Type*} {P : Type*} [AddCommGroup P] [Module ℤ_[p] P]
    [Module.Free ℤ_[p] P] [Module.Finite ℤ_[p] P]
    (s : ι → P →ₗ[ℤ_[p]] P) (a : ι → ℤ_[p])
    (hW : ∀ (i : ι) (x : P), s i x - x ∈ ⨅ j, LinearMap.ker (s j - a j • LinearMap.id))
    (hrank : 2 * Module.finrank ℤ_[p] ↥(⨅ j, LinearMap.ker (s j - a j • LinearMap.id)) =
      Module.finrank ℤ_[p] P)
    (i₀ : ι) (hi₀ : ¬ (p : ℤ_[p]) ∣ a i₀ - 1)
    {G : Type*} [AddCommGroup G] (π : P →+ G)
    (hker : ∀ x : P, π x = 0 ↔ ∃ y : P, x = (p : ℤ_[p]) • y)
    (g : ι → G → G) (hg : ∀ (i : ι) (x : P), π (s i x) = g i (π x))
    (c : ι → ℕ) (hc : ∀ i, (p : ℤ_[p]) ∣ a i - (c i : ℤ_[p])) :
    Set.ncard {y : G | y ∈ π.range ∧ ∀ i, g i y = c i • y} ^ 2 = Nat.card ↥π.range := by p2m_exact_reverting @_root_.P2MW.S_PadicInt_ncard_setOf_forall_apply_eq_nsmul_sq_eq_card_range_of_forall_sub_mem_iInf_ker.solution
