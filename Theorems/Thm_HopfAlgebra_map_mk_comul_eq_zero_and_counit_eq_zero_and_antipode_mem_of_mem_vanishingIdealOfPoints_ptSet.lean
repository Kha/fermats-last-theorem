import Mathlib
import Definitions.Def_HopfAlgebra_CharacterClosure
import P2M.Util
import P2M.Sol.S_HopfAlgebra_map_mk_comul_eq_zero_and_counit_eq_zero_and_antipode_mem_of_mem_vanishingIdealOfPoints_ptSet
set_option autoImplicit false
open scoped TensorProduct
theorem HopfAlgebra.map_mk_comul_eq_zero_and_counit_eq_zero_and_antipode_mem_of_mem_vanishingIdealOfPoints_ptSet
    {F : Type*} [Field F] {A : Type*} [CommRing A] [HopfAlgebra F A]
    {L : Type*} [Field L] [Algebra F L]
    (S : Submonoid (WithConv (A →ₐ[F] L)))
    (hsep : ∀ x : TensorProduct F (HopfAlgebra.pointQuot S) (HopfAlgebra.pointQuot S),
      (∀ (ν ν' : A →ₐ[F] L) (hν : ν ∈ HopfAlgebra.ptSet S) (hν' : ν' ∈ HopfAlgebra.ptSet S),
        HopfAlgebra.evalPair (HopfAlgebra.ptSet S) ν ν' hν hν' x = 0) → x = 0)
    (hinv : ∀ ν ∈ HopfAlgebra.ptSet S, ∃ ν' ∈ HopfAlgebra.ptSet S,
      ν'.toLinearMap = ν.toLinearMap ∘ₗ HopfAlgebraStruct.antipode (R := F)) :
    (∀ a ∈ HopfAlgebra.vanishingIdealOfPoints (HopfAlgebra.ptSet S),
      Algebra.TensorProduct.map
        (Ideal.Quotient.mkₐ F (HopfAlgebra.vanishingIdealOfPoints (HopfAlgebra.ptSet S)))
        (Ideal.Quotient.mkₐ F (HopfAlgebra.vanishingIdealOfPoints (HopfAlgebra.ptSet S)))
        (Coalgebra.comul (R := F) a) = 0) ∧
    (∀ a ∈ HopfAlgebra.vanishingIdealOfPoints (HopfAlgebra.ptSet S), Coalgebra.counit (R := F) a = 0) ∧
    (∀ a ∈ HopfAlgebra.vanishingIdealOfPoints (HopfAlgebra.ptSet S),
      HopfAlgebraStruct.antipode (R := F) a ∈ HopfAlgebra.vanishingIdealOfPoints (HopfAlgebra.ptSet S)) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_map_mk_comul_eq_zero_and_counit_eq_zero_and_antipode_mem_of_mem_vanishingIdealOfPoints_ptSet.solution
