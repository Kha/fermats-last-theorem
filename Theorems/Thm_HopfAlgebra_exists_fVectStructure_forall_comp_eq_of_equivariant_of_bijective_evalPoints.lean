import Mathlib
import Definitions.Def_HopfAlgebra_FVectStructure
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_fVectStructure_forall_comp_eq_of_equivariant_of_bijective_evalPoints

set_option autoImplicit false
open scoped TensorProduct

theorem HopfAlgebra.exists_fVectStructure_forall_comp_eq_of_equivariant_of_bijective_evalPoints
    (D : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (A : Type) [CommRing A] [HopfAlgebra ↥(IntermediateField.fixedField D) A]
    [Module.Finite ↥(IntermediateField.fixedField D) A]
    [Finite (WithConv (A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ))]
    (hev : Function.Bijective
      (Algebra.TensorProduct.lift
        (Algebra.ofId (AlgebraicClosure ℚ) (WithConv (A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ) → AlgebraicClosure ℚ))
        (Pi.algHom ↥(IntermediateField.fixedField D) _
          fun ν : WithConv (A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ) =>
            (WithConv.ofConv ν : A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ))
        (fun _ _ => Commute.all _ _) :
        AlgebraicClosure ℚ ⊗[↥(IntermediateField.fixedField D)] A →ₐ[AlgebraicClosure ℚ]
          (WithConv (A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ) → AlgebraicClosure ℚ)))
    (F : Type*) [Field F]
    (act : F → (WithConv (A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ) →* WithConv (A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ)))
    (hact : ∀ a : F, ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ D →
      ∀ ν ν' : WithConv (A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ),
        (∀ x : A, WithConv.ofConv ν' x = σ (WithConv.ofConv ν x)) →
        ∀ x : A, WithConv.ofConv (act a ν') x = σ (WithConv.ofConv (act a ν) x))
    (hadd : ∀ (a b : F) (ν : WithConv (A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ)), act (a + b) ν = act a ν * act b ν)
    (hzero : ∀ ν : WithConv (A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ), act 0 ν = 1)
    (hmul : ∀ (a b : F) (ν : WithConv (A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ)), act (a * b) ν = act a (act b ν))
    (hone : ∀ ν : WithConv (A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ), act 1 ν = ν) :
    ∃ fv : HopfAlgebra.FVectStructure F ↥(IntermediateField.fixedField D) A,
      ∀ (a : F) (ν : WithConv (A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ)),
        WithConv.toConv ((WithConv.ofConv ν).comp (fv.act a : A →ₐ[↥(IntermediateField.fixedField D)] A)) = act a ν := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_fVectStructure_forall_comp_eq_of_equivariant_of_bijective_evalPoints.solution
