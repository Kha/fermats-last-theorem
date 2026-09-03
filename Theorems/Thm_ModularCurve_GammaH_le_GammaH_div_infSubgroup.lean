import Mathlib
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_XHDifferentialsModL
import P2M.Util
import P2M.Sol.S_ModularCurve_GammaH_le_GammaH_div_infSubgroup

set_option autoImplicit false

open ModularCurve
open scoped MatrixGroups

theorem ModularCurve.GammaH_le_GammaH_div_infSubgroup
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) :
    CohCarrier.GammaH M H ≤ CohCarrier.GammaH (M / p) (infSubgroup p M H hpM) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_GammaH_le_GammaH_div_infSubgroup.solution
