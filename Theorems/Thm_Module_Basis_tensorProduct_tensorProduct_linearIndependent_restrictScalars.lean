import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import P2M.Util
import P2M.Sol.S_Module_Basis_tensorProduct_tensorProduct_linearIndependent_restrictScalars

open scoped TensorProduct
theorem Module.Basis.tensorProduct_tensorProduct_linearIndependent_restrictScalars
    (R : Type) (K : Type) (A : Type) [CommRing R] [CommRing K] [Algebra R K] [CommRing A]
    [Algebra K A] [Algebra R A] [IsScalarTower R K A]
    (hinj : Function.Injective (algebraMap R K))
    {n : ℕ} (b : Module.Basis (Fin n) K A) :
    LinearIndependent R ((b.tensorProduct (b.tensorProduct b)) :
      Fin n × Fin n × Fin n → A ⊗[K] (A ⊗[K] A)) := by p2m_exact_reverting @_root_.P2MW.S_Module_Basis_tensorProduct_tensorProduct_linearIndependent_restrictScalars.solution
