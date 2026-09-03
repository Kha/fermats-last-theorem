import Mathlib.RingTheory.HopfAlgebra.TensorProduct
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.Flat.Basic
import Theorems.Thm_HopfAlgebra_isReduced_of_finiteType_of_isAlgClosed_of_charZero
import P2M.Util
namespace P2MW.S_HopfAlgebra_isReduced_of_finiteType_of_charZero

set_option maxHeartbeats 3200000
open scoped TensorProduct

theorem solution
    (K : Type*) [Field K] [CharZero K]
    (A : Type*) [CommRing A] [HopfAlgebra K A] [Algebra.FiniteType K A] :
    IsReduced A := by
  let Ω := AlgebraicClosure K

  haveI : IsReduced (Ω ⊗[K] A) :=
    HopfAlgebra.isReduced_of_finiteType_of_isAlgClosed_of_charZero Ω (Ω ⊗[K] A)

  have hinj : Function.Injective
      (Algebra.TensorProduct.includeRight : A →ₐ[K] Ω ⊗[K] A) :=
    Algebra.TensorProduct.includeRight_injective (R := K) (A := Ω) (B := A)
      (algebraMap K Ω).injective
  exact isReduced_of_injective
    (Algebra.TensorProduct.includeRight : A →ₐ[K] Ω ⊗[K] A).toRingHom hinj
