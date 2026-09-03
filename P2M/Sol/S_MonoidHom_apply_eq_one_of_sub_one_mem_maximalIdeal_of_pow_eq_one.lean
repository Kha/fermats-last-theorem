import Mathlib
import Theorems.Thm_IsLocalRing_eq_one_of_pow_eq_one_of_sub_one_mem_maximalIdeal
import P2M.Util
namespace P2MW.S_MonoidHom_apply_eq_one_of_sub_one_mem_maximalIdeal_of_pow_eq_one

set_option autoImplicit false

universe u w

open IsLocalRing

theorem solution {G : Type u} {A : Type w} [Group G] [CommRing A] [IsLocalRing A]
    (χ : G →* Aˣ) (g : G) (hprin : (χ g : A) - 1 ∈ IsLocalRing.maximalIdeal A)
    {n : ℕ} (hn : IsUnit (n : A)) (hgn : g ^ n = 1) : χ g = 1 := by
  ext
  refine IsLocalRing.eq_one_of_pow_eq_one_of_sub_one_mem_maximalIdeal hprin hn ?_
  have h := congrArg (Units.val) (map_pow χ g n ▸ (congrArg χ hgn).trans (map_one χ))
  simpa using h
