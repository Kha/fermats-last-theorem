import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Mathlib.LinearAlgebra.TensorProduct.Prod
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_baseChangeIsos_structureSheaf

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_baseChangeIsos_structureSheaf
    {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))
    (A : Type u) [CommRing A] [Algebra R A] :
    ∃ (e0 : (A ⊗[R] (𝒱.cover c).A0) ≃ₐ[A]
          ((𝒱.pullback c A).cover (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))).A0)
      (e1 : (A ⊗[R] (𝒱.cover c).A1) ≃ₐ[A]
          ((𝒱.pullback c A).cover (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))).A1)
      (e01 : (A ⊗[R] (𝒱.cover c).A01) ≃ₐ[A]
          ((𝒱.pullback c A).cover (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))).A01)
      (eH0 : LinearMap.ker ((𝒱.structureSheafSections c).cechDiff.baseChange A) ≃ₗ[A]
          ((𝒱.pullback c A).structureSheafSections
            (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))).H0)
      (eH1 : ((A ⊗[R] (𝒱.cover c).A01) ⧸ LinearMap.range ((𝒱.structureSheafSections c).cechDiff.baseChange A))
          ≃ₗ[A] ((𝒱.pullback c A).structureSheafSections
            (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))).H1),
      (∀ s, e0 ((1 : A) ⊗ₜ[R] s) = ((pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A)).app 𝒱.U0).hom s) ∧
      (∀ s, e1 ((1 : A) ⊗ₜ[R] s) = ((pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A)).app 𝒱.U1).hom s) ∧
      (∀ s, e01 ((1 : A) ⊗ₜ[R] s)
          = ((pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A)).app (𝒱.U0 ⊓ 𝒱.U1)).hom s) ∧
      (∀ x, ((eH0 x : _ × _)) = (e0 (TensorProduct.prodRight R A A _ _ x.1).1,
          e1 (TensorProduct.prodRight R A A _ _ x.1).2)) ∧
      (∀ y, eH1 (Submodule.Quotient.mk y) = Submodule.Quotient.mk (e01 y)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_baseChangeIsos_structureSheaf.solution
