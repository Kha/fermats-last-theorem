import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_FormallyUnramified_nonempty_ringHom_int

theorem Algebra.FormallyUnramified.nonempty_ringHom_int
    (B : Type*) [CommRing B] [Nontrivial B] [Module.Finite ℤ B] [Module.Flat ℤ B]
    [Algebra.FormallyUnramified ℤ B] : Nonempty (B →+* ℤ) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_FormallyUnramified_nonempty_ringHom_int.solution
