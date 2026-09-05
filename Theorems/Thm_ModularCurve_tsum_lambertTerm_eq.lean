module

public import Definitions.Def_ModularCurve_TateFormal
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
import P2M.Util
import P2M.Sol.S_ModularCurve_tsum_lambertTerm_eq

@[expose] public section
attribute [-instance] ModularCurve.instIsElliptic_tateBase
attribute [-simp] ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst

open ModularCurve
theorem ModularCurve.tsum_lambertTerm_eq (K : Type*) [Field K] (p : ℕ) [NeZero p] (c : ℕ → ℕ) :
    ∑' n : ℕ, ((c n : ℕ) : LaurentSeries K) *
        ((HahnSeries.single (p : ℤ) (1 : K)) ^ n / (1 - (HahnSeries.single (p : ℤ) (1 : K)) ^ n)) =
      qExpand K p (laurentOfInt K (PowerSeries.mk fun m => ∑ d ∈ m.divisors, (c d : ℤ))) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_tsum_lambertTerm_eq.solution
