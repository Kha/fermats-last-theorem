import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import P2M.Util
import P2M.Sol.S_Rep_finrank_invariants_res_dualTwist_eq

set_option autoImplicit false
open CategoryTheory Module groupCohomology ExtCitation
theorem Rep.finrank_invariants_res_dualTwist_eq
    {p : ℕ} [Fact p.Prime] {H : Type} [Group H]
    (r : H →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) [FiniteDimensional (ZMod p) M] :
    finrank (ZMod p) (Rep.res r (M.dualTwist (cycloChar p))).ρ.invariants
      = finrank (ZMod p) ((Rep.res r M).dualTwist ((cycloChar p).comp r)).ρ.invariants := by p2m_exact_reverting @_root_.P2MW.S_Rep_finrank_invariants_res_dualTwist_eq.solution
