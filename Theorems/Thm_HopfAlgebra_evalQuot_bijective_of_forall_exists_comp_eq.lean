import Mathlib
import Definitions.Def_HopfAlgebra_CharacterClosure
import P2M.Util
import P2M.Sol.S_HopfAlgebra_evalQuot_bijective_of_forall_exists_comp_eq

set_option autoImplicit false
open scoped TensorProduct

theorem HopfAlgebra.evalQuot_bijective_of_forall_exists_comp_eq
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
    (S : Submonoid (WithConv (A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ)))
    (hstab : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ D → ∀ ν ∈ S, ∃ ν' ∈ S,
      ∀ a : A, WithConv.ofConv ν' a = σ (WithConv.ofConv ν a)) :
    Function.Bijective (HopfAlgebra.evalQuot S) ∧
      ∀ x : HopfAlgebra.pointQuot S ⊗[↥(IntermediateField.fixedField D)] HopfAlgebra.pointQuot S,
        (∀ ν ν' (hν : ν ∈ HopfAlgebra.ptSet S) (hν' : ν' ∈ HopfAlgebra.ptSet S),
            HopfAlgebra.evalPair (HopfAlgebra.ptSet S) ν ν' hν hν' x = 0) → x = 0 := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_evalQuot_bijective_of_forall_exists_comp_eq.solution
