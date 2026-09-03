import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_RankinSelberg_mk_heckeRecursionSeq_mul_heckeRecursionSeq_mul_coe_rsEulerPoly_eq_and_hasSum

set_option autoImplicit false

open UnramifiedWhittaker LanglandsTunnell.RankinSelberg

theorem LanglandsTunnell.RankinSelberg.mk_heckeRecursionSeq_mul_heckeRecursionSeq_mul_coe_rsEulerPoly_eq_and_hasSum
    (N lam om lam' om' : ℂ) :
    PowerSeries.mk (fun m : ℕ => heckeRecursionSeq N lam om m * heckeRecursionSeq N lam' om' m) *
        (rsEulerPoly (lam / N) (om / N) (lam' / N) (om' / N) 0 : PowerSeries ℂ) =
      1 - PowerSeries.C (om / N * (om' / N)) * PowerSeries.X ^ 2 ∧
    (∀ m : ℕ, ‖heckeRecursionSeq N lam om m‖ ≤ (max 1 (‖lam / N‖ + ‖om / N‖)) ^ m) ∧
    ∀ x : ℂ, ‖x‖ * (max 1 (‖lam / N‖ + ‖om / N‖) * max 1 (‖lam' / N‖ + ‖om' / N‖)) < 1 →
      (rsEulerPoly (lam / N) (om / N) (lam' / N) (om' / N) 0).eval x ≠ 0 ∧
      HasSum (fun m : ℕ => heckeRecursionSeq N lam om m * heckeRecursionSeq N lam' om' m * x ^ m)
        ((1 - om / N * (om' / N) * x ^ 2) / (rsEulerPoly (lam / N) (om / N) (lam' / N) (om' / N) 0).eval x) ∧
      HasSum (fun m : ℤ => torusFactor N lam om m * torusFactor N lam' om' m * x ^ m)
        ((1 - om / N * (om' / N) * x ^ 2) / (rsEulerPoly (lam / N) (om / N) (lam' / N) (om' / N) 0).eval x) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_RankinSelberg_mk_heckeRecursionSeq_mul_heckeRecursionSeq_mul_coe_rsEulerPoly_eq_and_hasSum.solution
