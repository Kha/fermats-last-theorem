import Mathlib
import Definitions.Def_HopfAlgebra_CharacterClosure
import P2M.Util
import P2M.Sol.S_HopfAlgebra_tensorProduct_pointQuot_eq_zero_of_forall_evalPair_eq_zero_of_bijective_evalQuot

set_option autoImplicit false

open scoped TensorProduct

theorem HopfAlgebra.tensorProduct_pointQuot_eq_zero_of_forall_evalPair_eq_zero_of_bijective_evalQuot
    {F : Type*} [Field F] {A : Type*} [CommRing A] [Bialgebra F A]
    {L : Type*} [Field L] [Algebra F L]
    (S : Submonoid (WithConv (A →ₐ[F] L))) [Finite ↥S]
    (hev : Function.Bijective (HopfAlgebra.evalQuot S))
    (x : HopfAlgebra.pointQuot S ⊗[F] HopfAlgebra.pointQuot S)
    (hx : ∀ (ν ν' : A →ₐ[F] L) (hν : ν ∈ HopfAlgebra.ptSet S) (hν' : ν' ∈ HopfAlgebra.ptSet S),
      HopfAlgebra.evalPair (HopfAlgebra.ptSet S) ν ν' hν hν' x = 0) :
    x = 0 := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_tensorProduct_pointQuot_eq_zero_of_forall_evalPair_eq_zero_of_bijective_evalQuot.solution
