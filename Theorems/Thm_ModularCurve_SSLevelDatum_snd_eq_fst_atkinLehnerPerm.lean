import Definitions.Def_ModularCurve_SSDegeneracyHecke
import P2M.Util
import P2M.Sol.S_ModularCurve_SSLevelDatum_snd_eq_fst_atkinLehnerPerm

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.SSLevelDatum.snd_eq_fst_atkinLehnerPerm
    {p : ℕ} [Fact p.Prime] {K : Type*} [Field K] [CharP K p] [DecidableEq K] {M s : ℕ} [NeZero M] [NeZero s]
    (X : SSLevelDatum p K M s) (W : ↥(ssPlaces p (M * s) K)) :
    X.snd W = X.fst (X.atkinLehnerPerm W) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_SSLevelDatum_snd_eq_fst_atkinLehnerPerm.solution
