module

public import Mathlib
public import Definitions.Def_ModularCurve_LegendreJ
public import P2M.Util
public import P2M.Sol.S_ModularCurve_legendreJ_eq_ofNat_iff

@[expose] public section

open ModularCurve
theorem ModularCurve.legendreJ_eq_ofNat_iff {K : Type*} [Field K] (h2 : (2 : K) ≠ 0)
    {t : K} (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    legendreJ t = 1728 ↔ t = -1 ∨ t = 2 ∨ t = 2⁻¹ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_legendreJ_eq_ofNat_iff.solution
