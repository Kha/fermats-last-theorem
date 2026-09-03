import Mathlib
import Definitions.Def_LocalLanglands_CartanDecomposition
import P2M.Util
import P2M.Sol.S_LocalGL2_cartanDiag_cartanRel_iff

open Matrix LocalGL2
theorem LocalGL2.cartanDiag_cartanRel_iff
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {ϖ : R} (hϖ : Irreducible ϖ) {a b a' b' : ℕ}
    (hab : a ≤ b) (hab' : a' ≤ b') :
    CartanRel (cartanDiag ϖ a b) (cartanDiag ϖ a' b') ↔ a = a' ∧ b = b' := by p2m_exact_reverting @_root_.P2MW.S_LocalGL2_cartanDiag_cartanRel_iff.solution
