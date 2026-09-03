import Mathlib
import Definitions.Def_ModularCurve_SSDegeneracyHecke
import P2M.Util
import P2M.Sol.S_ModularCurve_SSLevelDatum_degeneracyData_b_eq_a_atkinLehnerPerm

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.SSLevelDatum.degeneracyData_b_eq_a_atkinLehnerPerm
    (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [CharP K p] [DecidableEq K] (M s : ℕ) [NeZero M] [NeZero s]
    (X : SSLevelDatum p K M s) (W : ↥(ssPlaces p (M * s) K)) :
    X.degeneracyData.b W = X.degeneracyData.a (X.atkinLehnerPerm W) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_SSLevelDatum_degeneracyData_b_eq_a_atkinLehnerPerm.solution
