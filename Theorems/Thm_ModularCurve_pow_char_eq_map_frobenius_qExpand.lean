module

public import Definitions.Def_ModularCurve_X0
public import P2M.Util
public import P2M.Sol.S_ModularCurve_pow_char_eq_map_frobenius_qExpand

@[expose] public section

open ModularCurve
theorem ModularCurve.pow_char_eq_map_frobenius_qExpand {R : Type*} [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p]
    (s : LaurentSeries R) :
    s ^ p = (qExpand R p s).map (frobenius R p) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_pow_char_eq_map_frobenius_qExpand.solution
