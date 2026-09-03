import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GroupCohomology_Selmer
import Definitions.Def_GroupCohomology_ContinuousH1
import P2M.Util
import P2M.Sol.S_groupCohomology_locRes_extArithLoc_apply_mem_continuousH1
set_option autoImplicit false
open CategoryTheory groupCohomology ExtCitation
theorem groupCohomology.locRes_extArithLoc_apply_mem_continuousH1
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes)
    (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (x : H1 M) (hx : x ∈ continuousH1 (MonoidHom.id _) M) (v : extArithIndex S) :
    (locRes (extArithLoc S) M v).hom x ∈
      continuousH1 (extArithLoc S v) (Rep.res (extArithLoc S v) M) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_locRes_extArithLoc_apply_mem_continuousH1.solution
