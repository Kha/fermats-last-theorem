import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_adjoin_range_eq_top_and_finiteType_of_forall_existsUnique_comp_eq

set_option autoImplicit false

universe u

theorem Algebra.adjoin_range_eq_top_and_finiteType_of_forall_existsUnique_comp_eq
    {A₀ : Type u} [CommRing A₀] {A : Type u} [CommRing A] [Algebra A₀ A]
    {B₀ : Type u} [CommRing B₀] [Algebra A₀ B₀] {B : Type u} [CommRing B] [Algebra A B]
    (φ : B₀ →+* B) (hφ : φ.comp (algebraMap A₀ B₀) = (algebraMap A B).comp (algebraMap A₀ A))
    (hUP : ∀ (T : Type u) [CommRing T] [Algebra A T] (g : B₀ →+* T),
        g.comp (algebraMap A₀ B₀) = (algebraMap A T).comp (algebraMap A₀ A) →
        ∃! h : B →ₐ[A] T, h.toRingHom.comp φ = g) :
    Algebra.adjoin A (Set.range φ) = ⊤ ∧ (Algebra.FiniteType A₀ B₀ → Algebra.FiniteType A B) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_adjoin_range_eq_top_and_finiteType_of_forall_existsUnique_comp_eq.solution
