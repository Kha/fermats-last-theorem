import Mathlib
import P2M.Util
import P2M.Sol.S_Module_Flat_exists_fg_subalgebra_flat_tensorProduct

open TensorProduct

theorem Module.Flat.exists_fg_subalgebra_flat_tensorProduct
    {R₀ R B₀ : Type*} [CommRing R₀] [CommRing R] [CommRing B₀]
    [Algebra R₀ R] [Algebra R₀ B₀] [Algebra.FinitePresentation R₀ B₀]
    [Module.Flat R (R ⊗[R₀] B₀)] (s : Finset R) :
    ∃ R₁ : Subalgebra R₀ R, R₁.FG ∧ (↑s : Set R) ⊆ R₁ ∧ Module.Flat R₁ (R₁ ⊗[R₀] B₀) := by p2m_exact_reverting @_root_.P2MW.S_Module_Flat_exists_fg_subalgebra_flat_tensorProduct.solution
