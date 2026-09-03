import Mathlib
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_bialgHom_forall_comp_eq_of_equivariant_of_bijective_evalPoints

set_option autoImplicit false
open scoped TensorProduct

theorem HopfAlgebra.exists_bialgHom_forall_comp_eq_of_equivariant_of_bijective_evalPoints
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
    (φ : WithConv (A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ) →* WithConv (A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ))
    (hφ : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ D →
      ∀ ν ν' : WithConv (A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ),
        (∀ a : A, WithConv.ofConv ν' a = σ (WithConv.ofConv ν a)) →
        ∀ a : A, WithConv.ofConv (φ ν') a = σ (WithConv.ofConv (φ ν) a)) :
    ∃ u : A →ₐc[↥(IntermediateField.fixedField D)] A,
      ∀ ν : WithConv (A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ),
        WithConv.toConv ((WithConv.ofConv ν).comp (u : A →ₐ[↥(IntermediateField.fixedField D)] A)) = φ ν := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_bialgHom_forall_comp_eq_of_equivariant_of_bijective_evalPoints.solution
