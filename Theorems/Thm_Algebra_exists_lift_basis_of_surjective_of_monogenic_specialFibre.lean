import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_exists_lift_basis_of_surjective_of_monogenic_specialFibre

set_option autoImplicit false

open Polynomial

universe u v w x

theorem Algebra.exists_lift_basis_of_surjective_of_monogenic_specialFibre
    (R' : Type u) [CommRing R'] [IsLocalRing R'] (R : Type v) [CommRing R] [IsLocalRing R]
    (π : R' →+* R) (hπ : Function.Surjective π)
    (C : Type w) [CommRing C] [Algebra R C] (ι : Type x) [Fintype ι]
    (e : Module.Basis ι R C) (i₀ : ι) (he : e i₀ = 1)
    (hmono : ∃ y : C, ∀ z : C, ∃ q : R[X],
      z - aeval y q ∈ (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R C)) :
    ∃ (C' : Type u) (_ : CommRing C') (_ : Algebra R' C') (e' : Module.Basis ι R' C')
      (σ : C' →+* C),
      e' i₀ = 1 ∧ (∀ r, σ (algebraMap R' C' r) = algebraMap R C (π r)) ∧ ∀ i, σ (e' i) = e i := by p2m_exact_reverting @_root_.P2MW.S_Algebra_exists_lift_basis_of_surjective_of_monogenic_specialFibre.solution
