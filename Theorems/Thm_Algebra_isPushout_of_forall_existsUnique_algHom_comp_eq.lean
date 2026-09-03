import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_isPushout_of_forall_existsUnique_algHom_comp_eq

set_option autoImplicit false

universe u

theorem Algebra.isPushout_of_forall_existsUnique_algHom_comp_eq
    {R S R' S' : Type u} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    [Algebra R S] [Algebra R R'] [Algebra S S'] [Algebra R' S'] [Algebra R S']
    [IsScalarTower R S S'] [IsScalarTower R R' S']
    (h : ∀ (T : Type u) [CommRing T] [Algebra R' T] (g : S →+* T),
      g.comp (algebraMap R S) = (algebraMap R' T).comp (algebraMap R R') →
        ∃! k : S' →ₐ[R'] T, k.toRingHom.comp (algebraMap S S') = g) :
    Algebra.IsPushout R S R' S' := by p2m_exact_reverting @_root_.P2MW.S_Algebra_isPushout_of_forall_existsUnique_algHom_comp_eq.solution
