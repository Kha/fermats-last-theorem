import Mathlib
import P2M.Util
import P2M.Sol.S_Representation_stable_eq_bot_or_top_of_trace_eq_of_det_eq_of_irreducible

theorem Representation.stable_eq_bot_or_top_of_trace_eq_of_det_eq_of_irreducible {k G V V₂ : Type*} [Field k] [Group G]
    [AddCommGroup V] [Module k V] [AddCommGroup V₂] [Module k V₂]
    (ρ₁ : Representation k G V) (ρ₂ : Representation k G V₂)
    (hfr₁ : Module.finrank k V = 2) (hfr₂ : Module.finrank k V₂ = 2)
    (hirr : ∀ W : Submodule k V, (∀ g, ∀ v ∈ W, ρ₁ g v ∈ W) → W = ⊥ ∨ W = ⊤)
    (htr : ∀ g, LinearMap.trace k V (ρ₁ g) = LinearMap.trace k V₂ (ρ₂ g))
    (hdet : ∀ g, LinearMap.det (ρ₁ g) = LinearMap.det (ρ₂ g)) :
    ∀ W : Submodule k V₂, (∀ g, ∀ v ∈ W, ρ₂ g v ∈ W) → W = ⊥ ∨ W = ⊤ := by p2m_exact_reverting @_root_.P2MW.S_Representation_stable_eq_bot_or_top_of_trace_eq_of_det_eq_of_irreducible.solution
