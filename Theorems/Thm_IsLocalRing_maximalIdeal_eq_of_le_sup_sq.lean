import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_maximalIdeal_eq_of_le_sup_sq

set_option autoImplicit false

universe u

open IsLocalRing

theorem IsLocalRing.maximalIdeal_eq_of_le_sup_sq
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (N : Ideal R) (hN : N ≤ maximalIdeal R) (h : maximalIdeal R ≤ N ⊔ maximalIdeal R ^ 2) :
    maximalIdeal R = N := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_maximalIdeal_eq_of_le_sup_sq.solution
