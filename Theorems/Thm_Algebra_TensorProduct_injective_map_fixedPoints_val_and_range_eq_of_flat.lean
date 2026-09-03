import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_TensorProduct_injective_map_fixedPoints_val_and_range_eq_of_flat

set_option autoImplicit false

open TensorProduct

theorem Algebra.TensorProduct.injective_map_fixedPoints_val_and_range_eq_of_flat
    (B A T : Type*) [CommRing B] [CommRing A] [Algebra B A] [CommRing T] [Algebra B T]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G A] [SMulCommClass G B A] [Module.Flat B T] :
    Function.Injective (Algebra.TensorProduct.map (AlgHom.id T T) (FixedPoints.subalgebra B A G).val) ∧
    Set.range (Algebra.TensorProduct.map (AlgHom.id T T) (FixedPoints.subalgebra B A G).val) =
      {x : T ⊗[B] A | ∀ g : G,
        Algebra.TensorProduct.map (AlgHom.id T T) (MulSemiringAction.toAlgHom B A g) x = x} := by p2m_exact_reverting @_root_.P2MW.S_Algebra_TensorProduct_injective_map_fixedPoints_val_and_range_eq_of_flat.solution
