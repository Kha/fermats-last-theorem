module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
import P2M.Util
public import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.LocalSubring

namespace P2MW.S_ValuationSubring_exists_root_mem_of_monic

set_option autoImplicit false

theorem solution {K : Type*} [Field K] [IsAlgClosed K]
    (A : ValuationSubring K) (f : Polynomial A) (hf : f.Monic) (hd : f.natDegree ≠ 0) :
    ∃ x : A, Polynomial.aeval (x : K) f = 0 := by
  have hdeg : (f.map (algebraMap A K)).degree ≠ 0 := by
    rw [hf.degree_map]
    intro h
    exact hd (Polynomial.natDegree_eq_zero_iff_degree_le_zero.mpr h.le)
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (f.map (algebraMap A K)) hdeg
  have hint : IsIntegral A x := by
    refine ⟨f, hf, ?_⟩
    rwa [Polynomial.IsRoot, Polynomial.eval_map] at hx
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  refine ⟨y, ?_⟩
  have hyx : (y : K) = x := hy
  rw [Polynomial.aeval_def, hyx]
  rwa [Polynomial.IsRoot, Polynomial.eval_map] at hx
end S_ValuationSubring_exists_root_mem_of_monic
end P2MW

public section
theorem ValuationSubring.exists_root_mem_of_monic {K : Type*} [Field K] [IsAlgClosed K]
    (A : ValuationSubring K) (f : Polynomial A) (hf : f.Monic) (hd : f.natDegree ≠ 0) :
    ∃ x : A, Polynomial.aeval (x : K) f = 0 := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_root_mem_of_monic.solution
end
