module

public import Definitions.Def_ModularCurve_TateFormal
public import P2M.Util
public import P2M.Sol.S_ModularCurve_j_tateLaurent

@[expose] public section

open PowerSeries HahnSeries ModularCurve
theorem ModularCurve.j_tateLaurent (K : Type*) [CommRing K] :
    (tateLaurent K).j = jqModC K := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_j_tateLaurent.solution
