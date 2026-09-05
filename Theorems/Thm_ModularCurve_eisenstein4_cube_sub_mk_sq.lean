module

public import Definitions.Def_ModularCurve_X0
import P2M.Util
import P2M.Sol.S_ModularCurve_eisenstein4_cube_sub_mk_sq

@[expose] public section

open ModularCurve
theorem ModularCurve.eisenstein4_cube_sub_mk_sq :
    eisenstein4 ^ 3 -
        (PowerSeries.mk fun n => if n = 0 then 1 else -504 * ∑ d ∈ n.divisors, (d : ℤ) ^ 5) ^ 2 =
      1728 * (PowerSeries.X * dedekindEtaUnit) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_eisenstein4_cube_sub_mk_sq.solution
