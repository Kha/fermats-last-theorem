import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_exists_isPrime_not_mem_ringKrullDim_quotient_eq_one

set_option autoImplicit false

universe u

open IsLocalRing

theorem IsLocalRing.exists_isPrime_not_mem_ringKrullDim_quotient_eq_one
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R] (hR : ¬ IsField R)
    (s : R) (hs : s ≠ 0) :
    ∃ q : Ideal R, q.IsPrime ∧ s ∉ q ∧ ringKrullDim (R ⧸ q) = 1 := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_exists_isPrime_not_mem_ringKrullDim_quotient_eq_one.solution
