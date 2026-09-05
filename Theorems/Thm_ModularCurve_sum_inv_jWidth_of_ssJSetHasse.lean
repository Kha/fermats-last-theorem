module

public import Mathlib
public import Definitions.Def_WeierstrassCurve_HasseInvariant
public import Definitions.Def_Polynomial_DeuringPolynomial
public import Definitions.Def_ModularCurve_LegendreJ
public import Definitions.Def_ModularCurve_JWidth
import P2M.Util
import P2M.Sol.S_ModularCurve_sum_inv_jWidth_of_ssJSetHasse

@[expose] public section

open Polynomial ModularCurve Finset
theorem ModularCurve.sum_inv_jWidth_of_ssJSetHasse (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (K : Type*) [Field K]
    [IsAlgClosed K] [CharP K q] [DecidableEq K] (S : Finset K)
    (hS : ∀ j, j ∈ S ↔ j ∈ ssJSetHasse q K) :
    ∑ j ∈ S, ((jWidth j : ℚ))⁻¹ = ((q : ℚ) - 1) / 12 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_sum_inv_jWidth_of_ssJSetHasse.solution
