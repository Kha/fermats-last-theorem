import Mathlib
import P2M.Util
import P2M.Sol.S_Representation_exists_basis_toMatrix_mem_subfield_of_trace_det_mem_of_hasEigenvalue

theorem Representation.exists_basis_toMatrix_mem_subfield_of_trace_det_mem_of_hasEigenvalue
    {Ω : Type*} [Field Ω] {V : Type*} [AddCommGroup V] [Module Ω V] {G : Type*} [Group G]
    (F : Subfield Ω) (ρ : G →* (V ≃ₗ[Ω] V)) (hV : Module.finrank Ω V = 2)
    (hirr : ∀ W : Submodule Ω V, (∀ g, ∀ v ∈ W, ρ g v ∈ W) → W = ⊥ ∨ W = ⊤)
    (htr : ∀ g, LinearMap.trace Ω V (ρ g).toLinearMap ∈ F)
    (hdet : ∀ g, LinearMap.det (ρ g).toLinearMap ∈ F)
    (g₀ : G) (a : Ω) (haF : a ∈ F) (hev : Module.End.HasEigenvalue (ρ g₀).toLinearMap a)
    (hns : (ρ g₀).toLinearMap ≠ a • LinearMap.id) :
    ∃ b : Module.Basis (Fin 2) Ω V,
      ∀ g (i j : Fin 2), LinearMap.toMatrix b b (ρ g).toLinearMap i j ∈ F := by p2m_exact_reverting @_root_.P2MW.S_Representation_exists_basis_toMatrix_mem_subfield_of_trace_det_mem_of_hasEigenvalue.solution
