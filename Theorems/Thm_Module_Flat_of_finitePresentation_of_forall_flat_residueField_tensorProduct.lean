import Mathlib
import P2M.Util
import P2M.Sol.S_Module_Flat_of_finitePresentation_of_forall_flat_residueField_tensorProduct

theorem Module.Flat.of_finitePresentation_of_forall_flat_residueField_tensorProduct
    {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [Algebra.FinitePresentation R A] [Algebra.FinitePresentation R B] [Module.Flat R B]
    (hfib : ∀ (p : Ideal R) [p.IsPrime],
      (Algebra.TensorProduct.map (AlgHom.id p.ResidueField p.ResidueField)
        (IsScalarTower.toAlgHom R A B)).toRingHom.Flat) :
    Module.Flat A B := by p2m_exact_reverting @_root_.P2MW.S_Module_Flat_of_finitePresentation_of_forall_flat_residueField_tensorProduct.solution
