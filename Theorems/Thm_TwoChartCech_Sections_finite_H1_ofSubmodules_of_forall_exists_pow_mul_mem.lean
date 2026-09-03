import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoChartCech
import P2M.Util
import P2M.Sol.S_TwoChartCech_Sections_finite_H1_ofSubmodules_of_forall_exists_pow_mul_mem

set_option autoImplicit false

universe u v

theorem TwoChartCech.Sections.finite_H1_ofSubmodules_of_forall_exists_pow_mul_mem
    {R : Type u} [CommRing R] {F : Type v} [CommRing F] [Algebra R F]
    (x y : F) (hxy : x * y = 1)
    (N0 N1 N01 : Submodule R F) (h0 : N0 ≤ N01) (h1 : N1 ≤ N01)
    (hx : ∀ m ∈ N0, x * m ∈ N0) (hy : ∀ m ∈ N1, y * m ∈ N1) (hy01 : ∀ m ∈ N01, y * m ∈ N01)
    (G0 : Finset F) (hG0 : (G0 : Set F) ⊆ N0)
    (hspan : (N0 : Set F) ⊆ Submodule.span ↥(Algebra.adjoin R ({x} : Set F)) (G0 : Set F))
    (hloc0 : ∀ z ∈ N01, ∃ k : ℕ, x ^ k * z ∈ N0) (hloc1 : ∀ z ∈ N01, ∃ k : ℕ, y ^ k * z ∈ N1) :
    Module.Finite R (TwoChartCech.Sections.ofSubmodules N0 N1 N01 h0 h1).H1 := by p2m_exact_reverting @_root_.P2MW.S_TwoChartCech_Sections_finite_H1_ofSubmodules_of_forall_exists_pow_mul_mem.solution
