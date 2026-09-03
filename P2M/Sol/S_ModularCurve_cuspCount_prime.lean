import Definitions.Def_ModularCurve_GenusNumerics
import Mathlib.Data.Nat.Totient
import P2M.Util
namespace P2MW.S_ModularCurve_cuspCount_prime

open ModularCurve

theorem solution {p : ℕ} (hp : p.Prime) : cuspCount p = 2 := by
  rw [cuspCount, hp.divisors, Finset.sum_pair hp.one_lt.ne]
  rw [Nat.div_one, Nat.div_self hp.pos]
  simp
