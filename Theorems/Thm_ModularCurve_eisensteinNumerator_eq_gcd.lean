import Definitions.Def_ModularCurve_ModularUnit
import P2M.Util
import P2M.Sol.S_ModularCurve_eisensteinNumerator_eq_gcd

open ModularCurve

theorem ModularCurve.eisensteinNumerator_eq_gcd (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) : eisensteinNumerator p = Nat.gcd ((p - 1) / 2) ((p ^ 2 - 1) / 24) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_eisensteinNumerator_eq_gcd.solution
