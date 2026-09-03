import Mathlib
import Definitions.Def_HopfAlgebra_CharacterClosure
import P2M.Util
import P2M.Sol.S_HopfAlgebra_lift_liftPoint_bijective_of_forall_exists_comp_eq
set_option autoImplicit false
open scoped TensorProduct
theorem HopfAlgebra.lift_liftPoint_bijective_of_forall_exists_comp_eq
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (D : Subgroup (L ≃ₐ[K] L)) (hD : IntermediateField.fixedField D = ⊥)
    {A : Type*} [CommRing A] [Algebra K A] [Module.Finite K A]
    {P : Type*} [Finite P] (pt : P → (A →ₐ[K] L)) (hpt : Function.Injective pt)
    (hev : Function.Bijective
      (Algebra.TensorProduct.lift (Algebra.ofId L (P → L)) (Pi.algHom K _ fun p : P => pt p)
        (fun _ _ => Commute.all _ _) : L ⊗[K] A →ₐ[L] (P → L)))
    (S : Set P) (hstab : ∀ σ : L ≃ₐ[K] L, σ ∈ D → ∀ p ∈ S, ∃ p' ∈ S, ∀ a : A, pt p' a = σ (pt p a)) :
    Function.Bijective
      (Algebra.TensorProduct.lift (Algebra.ofId L (↥S → L))
        (Pi.algHom K _ fun s : ↥S =>
          HopfAlgebra.liftPoint (pt '' S) (pt s.1) (Set.mem_image_of_mem pt s.2))
        (fun _ _ => Commute.all _ _) :
        L ⊗[K] (A ⧸ HopfAlgebra.vanishingIdealOfPoints (pt '' S)) →ₐ[L] (↥S → L)) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_lift_liftPoint_bijective_of_forall_exists_comp_eq.solution
