import Mathlib
import P2M.Util
import P2M.Sol.S_Submodule_moduleFinite_adjoin_eigenvalues_of_map_le_of_span_eq_top

set_option autoImplicit false

theorem Submodule.moduleFinite_adjoin_eigenvalues_of_map_le_of_span_eq_top
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (Λ : Submodule ℤ V) (hΛfg : Λ.FG) (hΛspan : Submodule.span ℂ (Λ : Set V) = ⊤)
    {J : Type*} (S : J → V →ₗ[ℂ] V) (hS : ∀ (j : J), ∀ x ∈ Λ, S j x ∈ Λ)
    (lam : J → ℂ) (v : V) (hv0 : v ≠ 0) (hv : ∀ j : J, S j v = lam j • v) :
    Module.Finite ℤ (Algebra.adjoin ℤ (Set.range lam)) := by p2m_exact_reverting @_root_.P2MW.S_Submodule_moduleFinite_adjoin_eigenvalues_of_map_le_of_span_eq_top.solution
