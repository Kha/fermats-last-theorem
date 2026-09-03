import Mathlib
import P2M.Util
import P2M.Sol.S_MvPowerSeries_expand_sub_pow_mem_span_natCast

set_option autoImplicit false

universe u v

theorem MvPowerSeries.expand_sub_pow_mem_span_natCast
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime]
    (hfrob : ∀ c : 𝓞, c ^ p - c ∈ Ideal.span {(p : 𝓞)})
    {σ : Type v} (f : MvPowerSeries σ 𝓞) :
    MvPowerSeries.expand p (Fact.out : p.Prime).ne_zero f - f ^ p ∈
      Ideal.span {(p : MvPowerSeries σ 𝓞)} := by p2m_exact_reverting @_root_.P2MW.S_MvPowerSeries_expand_sub_pow_mem_span_natCast.solution
