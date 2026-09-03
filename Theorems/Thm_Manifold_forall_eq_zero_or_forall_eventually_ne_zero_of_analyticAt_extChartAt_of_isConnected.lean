import Mathlib
import P2M.Util
import P2M.Sol.S_Manifold_forall_eq_zero_or_forall_eventually_ne_zero_of_analyticAt_extChartAt_of_isConnected

set_option autoImplicit false

open scoped Manifold ContDiff Topology

theorem Manifold.forall_eq_zero_or_forall_eventually_ne_zero_of_analyticAt_extChartAt_of_isConnected
    {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ, ℂ) ω M] [T2Space M]
    {W : Set M} (hW : IsOpen W) (hWc : IsConnected W) (g : M → ℂ)
    (hg : ∀ x ∈ W, AnalyticAt ℂ (fun z : ℂ => g ((extChartAt 𝓘(ℂ, ℂ) x).symm z)) (extChartAt 𝓘(ℂ, ℂ) x x)) :
    (∀ x ∈ W, g x = 0) ∨ (∀ x ∈ W, ∀ᶠ y in 𝓝[≠] x, g y ≠ 0) := by p2m_exact_reverting @_root_.P2MW.S_Manifold_forall_eq_zero_or_forall_eventually_ne_zero_of_analyticAt_extChartAt_of_isConnected.solution
