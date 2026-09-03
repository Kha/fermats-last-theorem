import Mathlib
import Definitions.Def_LocalLanglands_CartanDecomposition
import P2M.Util
import P2M.Sol.S_LocalGL2_exists_cartanRel_cartanDiag

open Matrix LocalGL2
theorem LocalGL2.exists_cartanRel_cartanDiag
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {ϖ : R} (hϖ : Irreducible ϖ)
    (g : Matrix (Fin 2) (Fin 2) R) (hg : g.det ≠ 0) :
    ∃ a b : ℕ, a ≤ b ∧ CartanRel g (cartanDiag ϖ a b) := by p2m_exact_reverting @_root_.P2MW.S_LocalGL2_exists_cartanRel_cartanDiag.solution
