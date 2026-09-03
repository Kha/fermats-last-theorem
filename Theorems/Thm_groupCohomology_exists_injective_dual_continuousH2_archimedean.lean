import Mathlib
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import P2M.Util
import P2M.Sol.S_groupCohomology_exists_injective_dual_continuousH2_archimedean

set_option autoImplicit false
open CategoryTheory Module groupCohomology ExtCitation
theorem groupCohomology.exists_injective_dual_continuousH2_archimedean
    (p : ℕ) [Fact p.Prime] (S : Finset Nat.Primes) :
    ∃ inv : continuousH2 (extArithLoc S (Sum.inl ()))
        (ofChar (k := ZMod p) ((cycloChar p).comp (extArithLoc S (Sum.inl ())))) →ₗ[ZMod p] ZMod p,
      Function.Injective inv := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_exists_injective_dual_continuousH2_archimedean.solution
