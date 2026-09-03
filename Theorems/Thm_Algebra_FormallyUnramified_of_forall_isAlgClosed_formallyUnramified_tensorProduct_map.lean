import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_FormallyUnramified_of_forall_isAlgClosed_formallyUnramified_tensorProduct_map

set_option autoImplicit false

universe u

open TensorProduct

theorem Algebra.FormallyUnramified.of_forall_isAlgClosed_formallyUnramified_tensorProduct_map
    {S : Type u} [CommRing S] {A B : Type u} [CommRing A] [CommRing B]
    [Algebra S A] [Algebra S B] [Algebra A B] [IsScalarTower S A B] [Algebra.FiniteType S B]
    (h : ∀ (k : Type u) [Field k] [IsAlgClosed k] [Algebra S k],
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S A B) (AlgHom.id S k)).toRingHom.FormallyUnramified) :
    Algebra.FormallyUnramified A B := by p2m_exact_reverting @_root_.P2MW.S_Algebra_FormallyUnramified_of_forall_isAlgClosed_formallyUnramified_tensorProduct_map.solution
