module

public import Mathlib
public import Definitions.Def_ModularCurve_LegendreJ
import P2M.Util
import P2M.Sol.S_ModularCurve_legendreJ_eq_legendreJ_iff

@[expose] public section

open ModularCurve
theorem ModularCurve.legendreJ_eq_legendreJ_iff {K : Type*} [Field K] [DecidableEq K] (h2 : (2 : K) ≠ 0)
    {s t : K} (hs0 : s ≠ 0) (hs1 : s ≠ 1) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    legendreJ s = legendreJ t ↔
      s ∈ ({t, 1 - t, t⁻¹, 1 - t⁻¹, (1 - t)⁻¹, 1 - (1 - t)⁻¹} : Finset K) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_legendreJ_eq_legendreJ_iff.solution
