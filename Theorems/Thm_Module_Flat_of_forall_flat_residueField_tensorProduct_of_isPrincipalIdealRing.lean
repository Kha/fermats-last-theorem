import Mathlib
import P2M.Util
import P2M.Sol.S_Module_Flat_of_forall_flat_residueField_tensorProduct_of_isPrincipalIdealRing

open scoped TensorProduct

universe u v w

theorem Module.Flat.of_forall_flat_residueField_tensorProduct_of_isPrincipalIdealRing
    {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {A : Type v} [CommRing A] [Algebra R A] {B : Type w} [CommRing B] [Algebra R B]
    [Algebra A B] [IsScalarTower R A B] [Module.Flat R A] [Module.Flat R B]
    (hfib : ∀ (p : Ideal R) [p.IsPrime],
      (Algebra.TensorProduct.map (AlgHom.id p.ResidueField p.ResidueField)
        (IsScalarTower.toAlgHom R A B)).toRingHom.Flat) :
    Module.Flat A B := by p2m_exact_reverting @_root_.P2MW.S_Module_Flat_of_forall_flat_residueField_tensorProduct_of_isPrincipalIdealRing.solution
