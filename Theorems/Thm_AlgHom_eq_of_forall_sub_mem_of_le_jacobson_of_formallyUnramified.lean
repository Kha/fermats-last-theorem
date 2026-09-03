import Mathlib
import P2M.Util
import P2M.Sol.S_AlgHom_eq_of_forall_sub_mem_of_le_jacobson_of_formallyUnramified

universe u v w

theorem AlgHom.eq_of_forall_sub_mem_of_le_jacobson_of_formallyUnramified
    {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
    [Algebra.EssFiniteType R A] [Algebra.FormallyUnramified R A]
    {B : Type w} [CommRing B] [Algebra R B]
    (I : Ideal B) (hI : I ≤ Ideal.jacobson ⊥)
    (f g : A →ₐ[R] B) (hfg : ∀ a : A, f a - g a ∈ I) :
    f = g := by p2m_exact_reverting @_root_.P2MW.S_AlgHom_eq_of_forall_sub_mem_of_le_jacobson_of_formallyUnramified.solution
