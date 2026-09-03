import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import P2M.Util
import P2M.Sol.S_IsIntegral_of_mem_span_of_apply_eq_smul

theorem IsIntegral.of_mem_span_of_apply_eq_smul {V : Type*} [AddCommGroup V] [Module ℂ V] (L : Submodule ℤ V) (hfg : L.FG) (T : V →ₗ[ℂ] V) (hTL : ∀ x ∈ L, T x ∈ L) {v : V} (hv : v ∈ Submodule.span ℂ (L : Set V)) (hv0 : v ≠ 0) {c : ℂ} (hTv : T v = c • v) : IsIntegral ℤ c := by p2m_exact_reverting @_root_.P2MW.S_IsIntegral_of_mem_span_of_apply_eq_smul.solution
