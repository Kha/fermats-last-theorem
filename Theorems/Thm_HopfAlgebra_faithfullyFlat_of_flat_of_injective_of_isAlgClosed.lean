import Mathlib
import P2M.Util
import P2M.Sol.S_HopfAlgebra_faithfullyFlat_of_flat_of_injective_of_isAlgClosed

set_option autoImplicit false

open scoped TensorProduct

universe u v w

theorem HopfAlgebra.faithfullyFlat_of_flat_of_injective_of_isAlgClosed
    {k : Type u} [Field k] [IsAlgClosed k]
    (K : Type v) [CommRing K] [HopfAlgebra k K] [Algebra.FiniteType k K]
    (H : Type w) [CommRing H] [HopfAlgebra k H] [Algebra.FiniteType k H]
    [Algebra K H] [IsScalarTower k K H] (hinj : Function.Injective (algebraMap K H))
    (hcomul : ∀ x : K, Coalgebra.comul (R := k) (algebraMap K H x) =
      TensorProduct.map (IsScalarTower.toAlgHom k K H).toLinearMap (IsScalarTower.toAlgHom k K H).toLinearMap
        (Coalgebra.comul (R := k) x))
    (hcounit : ∀ x : K, Coalgebra.counit (R := k) (algebraMap K H x) = Coalgebra.counit (R := k) x)
    [Module.Flat K H] :
    Module.FaithfullyFlat K H := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_faithfullyFlat_of_flat_of_injective_of_isAlgClosed.solution
