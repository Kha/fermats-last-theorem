import Mathlib
import P2M.Util
import P2M.Sol.S_MonoidHom_apply_eq_one_of_sub_one_mem_maximalIdeal_of_pow_eq_one

set_option autoImplicit false

universe u w

open IsLocalRing
theorem MonoidHom.apply_eq_one_of_sub_one_mem_maximalIdeal_of_pow_eq_one {G : Type u} {A : Type w} [Group G] [CommRing A] [IsLocalRing A]
    (χ : G →* Aˣ) (g : G) (hprin : (χ g : A) - 1 ∈ IsLocalRing.maximalIdeal A)
    {n : ℕ} (hn : IsUnit (n : A)) (hgn : g ^ n = 1) : χ g = 1 := by p2m_exact_reverting @_root_.P2MW.S_MonoidHom_apply_eq_one_of_sub_one_mem_maximalIdeal_of_pow_eq_one.solution
