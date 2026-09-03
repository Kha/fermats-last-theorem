import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Baire.CompleteMetrizable
import P2M.Util
namespace P2MW.S_LanglandsTunnell_exists_forall_le_eq_of_differentiable_of_forall_exists_forall_le_apply_eq

set_option autoImplicit false

open Filter Topology Set in

theorem solution
    (f : ℤ → ℂ → ℂ) (hf : ∀ c : ℤ, Differentiable ℂ (f c))
    (h : ∀ z : ℂ, ∃ c₀ : ℕ, ∀ c : ℤ, (c₀ : ℤ) ≤ c → f c z = f c₀ z) :
    ∃ c₀ : ℕ, ∀ c : ℤ, (c₀ : ℤ) ≤ c → f c = f c₀ := by
  set U : ℕ → Set ℂ := fun n => {z | ∀ c : ℤ, (n : ℤ) ≤ c → f c z = f n z} with hU
  have hclosed : ∀ n, IsClosed (U n) := by
    intro n
    have hrepr : U n = ⋂ c : ℤ, ⋂ (_ : (n : ℤ) ≤ c), {z | f c z = f n z} := by
      ext z
      simp only [hU, mem_setOf_eq, mem_iInter]
    rw [hrepr]
    exact isClosed_iInter fun c => isClosed_iInter fun _ =>
      isClosed_eq (hf c).continuous (hf n).continuous
  have hcover : ⋃ n, U n = univ := by
    ext z
    simp only [mem_iUnion, mem_univ, iff_true]
    obtain ⟨n, hn⟩ := h z
    exact ⟨n, hn⟩
  obtain ⟨n, z₀, hz₀⟩ := nonempty_interior_of_iUnion_of_closed hclosed hcover
  refine ⟨n, fun c hc => ?_⟩
  have hev : f c =ᶠ[𝓝 z₀] f n := by
    filter_upwards [mem_interior_iff_mem_nhds.mp hz₀] with z hz
    exact hz c hc
  exact ((hf c).differentiableOn.analyticOnNhd isOpen_univ).eq_of_eventuallyEq
    ((hf (n : ℤ)).differentiableOn.analyticOnNhd isOpen_univ) hev
