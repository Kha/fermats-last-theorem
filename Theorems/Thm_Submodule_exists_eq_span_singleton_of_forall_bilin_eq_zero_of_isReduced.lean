import Mathlib
import P2M.Util
import P2M.Sol.S_Submodule_exists_eq_span_singleton_of_forall_bilin_eq_zero_of_isReduced

set_option autoImplicit false

theorem Submodule.exists_eq_span_singleton_of_forall_bilin_eq_zero_of_isReduced
    {K : Type*} [Field K] {T : Type*} [CommRing T] [Algebra K T] [FiniteDimensional K T] [IsReduced T]
    {V : Type*} [AddCommGroup V] [Module K V] [Module T V] [IsScalarTower K T V]
    (e : V ≃ₗ[T] (Fin 2 → T))
    (B : V →ₗ[K] V →ₗ[K] K)
    (hBl : ∀ x, (∀ y, B x y = 0) → x = 0)
    (hBt : ∀ (t : T) (x y : V), B (t • x) y = B x (t • y))
    (N : Submodule T V) (hN : ∀ x ∈ N, ∀ y ∈ N, B x y = 0) :
    ∃ g : V, N = Submodule.span T {g} := by p2m_exact_reverting @_root_.P2MW.S_Submodule_exists_eq_span_singleton_of_forall_bilin_eq_zero_of_isReduced.solution
