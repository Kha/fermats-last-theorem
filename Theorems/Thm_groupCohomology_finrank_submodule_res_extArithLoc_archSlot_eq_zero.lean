import Definitions.Def_ExtEndgame_ProductionDatum
import P2M.Util
import P2M.Sol.S_groupCohomology_finrank_submodule_res_extArithLoc_archSlot_eq_zero

set_option autoImplicit false
open CategoryTheory Module groupCohomology ExtCitation
theorem groupCohomology.finrank_submodule_res_extArithLoc_archSlot_eq_zero
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (S : Finset Nat.Primes)
    (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    [FiniteDimensional (ZMod p) M] (u : Unit)
    (N : Submodule (ZMod p) (H1 (Rep.res (extArithLoc S (Sum.inl u)) M))) :
    finrank (ZMod p) N = 0 := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_finrank_submodule_res_extArithLoc_archSlot_eq_zero.solution
