module

public import Mathlib
public import Definitions.Def_ModularCurve_LegendreJ
public import P2M.Util
public import P2M.Sol.S_ModularCurve_exists_legendreJ_eq

@[expose] public section

open Polynomial ModularCurve
theorem ModularCurve.exists_legendreJ_eq {K : Type*} [Field K] [IsAlgClosed K] (h2 : (2 : K) ≠ 0) (j : K) :
    ∃ t : K, t ≠ 0 ∧ t ≠ 1 ∧ legendreJ t = j := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_legendreJ_eq.solution
