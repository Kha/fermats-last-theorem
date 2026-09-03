import Mathlib
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import P2M.Util
import P2M.Sol.S_Rep_nonempty_dualTwist_dualTwist_iso

set_option autoImplicit false
open CategoryTheory Module groupCohomology ExtCitation
theorem Rep.nonempty_dualTwist_dualTwist_iso
    {p : ℕ} [Fact p.Prime] {Γ : Type} [Group Γ] (χ : Γ →* (ZMod p)ˣ)
    (M : Rep (ZMod p) Γ) [FiniteDimensional (ZMod p) M] :
    Nonempty ((M.dualTwist χ).dualTwist χ ≅ M) := by p2m_exact_reverting @_root_.P2MW.S_Rep_nonempty_dualTwist_dualTwist_iso.solution
