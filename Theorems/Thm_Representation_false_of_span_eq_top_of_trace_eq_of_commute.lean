import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Dimension.Free
import P2M.Util
import P2M.Sol.S_Representation_false_of_span_eq_top_of_trace_eq_of_commute

theorem Representation.false_of_span_eq_top_of_trace_eq_of_commute
    {k G V V' : Type*} [Field k] [Monoid G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [AddCommGroup V'] [Module k V'] [FiniteDimensional k V']
    (h2 : Module.finrank k V = 2)
    (ρ : G →* Module.End k V) (hspan : Submodule.span k (Set.range ρ) = ⊤)
    (τ : G →* Module.End k V') (hcomm : ∀ g h : G, Commute (τ g) (τ h))
    (htr : ∀ g : G, LinearMap.trace k V (ρ g) = LinearMap.trace k V' (τ g)) : False := by p2m_exact_reverting @_root_.P2MW.S_Representation_false_of_span_eq_top_of_trace_eq_of_commute.solution
