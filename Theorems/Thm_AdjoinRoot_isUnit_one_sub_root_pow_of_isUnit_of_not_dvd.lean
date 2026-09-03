import Mathlib
import P2M.Util
import P2M.Sol.S_AdjoinRoot_isUnit_one_sub_root_pow_of_isUnit_of_not_dvd

set_option autoImplicit false

open Polynomial

universe u

theorem AdjoinRoot.isUnit_one_sub_root_pow_of_isUnit_of_not_dvd
    (𝒪 : Type u) [CommRing 𝒪] (m : ℕ) (hm : IsUnit ((m : ℕ) : 𝒪)) (j : ℕ) (hj : ¬ m ∣ j) :
    IsUnit (1 - AdjoinRoot.root (cyclotomic m 𝒪) ^ j) := by p2m_exact_reverting @_root_.P2MW.S_AdjoinRoot_isUnit_one_sub_root_pow_of_isUnit_of_not_dvd.solution
