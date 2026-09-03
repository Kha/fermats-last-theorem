import Mathlib
import P2M.Util
import P2M.Sol.S_WittVector_ringHom_map_frobenius_of_finite

set_option autoImplicit false

universe u v

theorem WittVector.ringHom_map_frobenius_of_finite
    (p : ℕ) [Fact p.Prime] {F : Type u} [Field F] [Finite F] [CharP F p]
    {k : Type v} [CommRing k] [CharP k p] [PerfectRing k p]
    (ι : WittVector p F →+* WittVector p k) (x : WittVector p F) :
    ι (WittVector.frobenius x) = WittVector.frobenius (ι x) := by p2m_exact_reverting @_root_.P2MW.S_WittVector_ringHom_map_frobenius_of_finite.solution
