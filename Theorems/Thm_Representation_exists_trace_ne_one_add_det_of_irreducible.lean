import Mathlib
import P2M.Util
import P2M.Sol.S_Representation_exists_trace_ne_one_add_det_of_irreducible

theorem Representation.exists_trace_ne_one_add_det_of_irreducible {k G V : Type*} [Field k] [Group G]
    [AddCommGroup V] [Module k V] (ρ : Representation k G V) (hfr : Module.finrank k V = 2)
    (hirr : ∀ W : Submodule k V, (∀ g, ∀ v ∈ W, ρ g v ∈ W) → W = ⊥ ∨ W = ⊤) :
    ∃ g, LinearMap.trace k V (ρ g) ≠ 1 + LinearMap.det (ρ g) := by p2m_exact_reverting @_root_.P2MW.S_Representation_exists_trace_ne_one_add_det_of_irreducible.solution
