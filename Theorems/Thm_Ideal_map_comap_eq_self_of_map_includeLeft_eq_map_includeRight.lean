import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.TensorProduct.Basic
import P2M.Util
import P2M.Sol.S_Ideal_map_comap_eq_self_of_map_includeLeft_eq_map_includeRight

set_option autoImplicit false

universe u

open TensorProduct

theorem Ideal.map_comap_eq_self_of_map_includeLeft_eq_map_includeRight
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [Module.FaithfullyFlat A B]
    (I : Ideal B)
    (hI : I.map (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[A] B) =
      I.map ((Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B) : B →+* B ⊗[A] B)) :
    (I.comap (algebraMap A B)).map (algebraMap A B) = I := by p2m_exact_reverting @_root_.P2MW.S_Ideal_map_comap_eq_self_of_map_includeLeft_eq_map_includeRight.solution
