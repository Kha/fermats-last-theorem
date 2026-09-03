import Mathlib
import P2M.Util
import P2M.Sol.S_WeightedMultigraph_slope_eq_zero_of_gradient_of_harmonic

set_option autoImplicit false

theorem WeightedMultigraph.slope_eq_zero_of_gradient_of_harmonic
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    (src tgt : E → V) (w : E → ℕ) (hw : ∀ e, 0 < w e)
    (vπ : Γ) (hvπ : vπ ≠ 0) (h : V → Γ) (s : E → ℤ)
    (hgrad : ∀ e, h (tgt e) - h (src e) = ((w e : ℤ) * s e) • vπ)
    (hharm : ∀ i, (∑ e ∈ Finset.univ.filter (fun e => tgt e = i), s e) =
                   ∑ e ∈ Finset.univ.filter (fun e => src e = i), s e) :
    ∀ e, s e = 0 := by p2m_exact_reverting @_root_.P2MW.S_WeightedMultigraph_slope_eq_zero_of_gradient_of_harmonic.solution
