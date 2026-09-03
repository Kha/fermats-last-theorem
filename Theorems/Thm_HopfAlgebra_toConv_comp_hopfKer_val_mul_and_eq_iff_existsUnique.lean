import Mathlib
import Definitions.Def_HopfAlgebra_HopfKerHopf
import P2M.Util
import P2M.Sol.S_HopfAlgebra_toConv_comp_hopfKer_val_mul_and_eq_iff_existsUnique

open scoped TensorProduct
theorem HopfAlgebra.toConv_comp_hopfKer_val_mul_and_eq_iff_existsUnique
    {R : Type*} [CommRing R] {A : Type*} [CommRing A] [HopfAlgebra R A] [Coalgebra.IsCocomm R A]
    {B : Type*} [CommRing B] [HopfAlgebra R B] [Module.Finite R B] [Module.Free R B]
    (π : A →ₐc[R] B) (hπ : Function.Surjective π)
    [Module.Flat R A] [Module.Flat R ↥(HopfAlgebra.hopfKer π)]
    (L : Type*) [CommRing L] [Algebra R L] :
    WithConv.toConv ((WithConv.ofConv (1 : WithConv (A →ₐ[R] L))).comp (HopfAlgebra.hopfKer π).val)
        = (1 : WithConv (↥(HopfAlgebra.hopfKer π) →ₐ[R] L)) ∧
    (∀ ν ν' : WithConv (A →ₐ[R] L),
        WithConv.toConv ((WithConv.ofConv (ν * ν')).comp (HopfAlgebra.hopfKer π).val)
          = WithConv.toConv ((WithConv.ofConv ν).comp (HopfAlgebra.hopfKer π).val)
            * WithConv.toConv ((WithConv.ofConv ν').comp (HopfAlgebra.hopfKer π).val)) ∧
    (∀ ν ν' : WithConv (A →ₐ[R] L),
        (WithConv.ofConv ν).comp (HopfAlgebra.hopfKer π).val
            = (WithConv.ofConv ν').comp (HopfAlgebra.hopfKer π).val
          ↔ ∃! χ : B →ₐ[R] L, ν' = ν * WithConv.toConv (χ.comp (π : A →ₐ[R] B))) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_toConv_comp_hopfKer_val_mul_and_eq_iff_existsUnique.solution
