import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverKaehler
import Mathlib.LinearAlgebra.TensorProduct.Prod
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_baseChangeIsos_kaehlerSections

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_baseChangeIsos_kaehlerSections
    {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))
    (A : Type u) [CommRing A] [Algebra R A] :
    ∃ (e0 : (A ⊗[R] Ω[(𝒱.cover c).A0⁄R]) ≃ₗ[A]
          Ω[((𝒱.pullback c A).cover (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))).A0⁄A])
      (e1 : (A ⊗[R] Ω[(𝒱.cover c).A1⁄R]) ≃ₗ[A]
          Ω[((𝒱.pullback c A).cover (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))).A1⁄A])
      (e01 : (A ⊗[R] Ω[(𝒱.cover c).A01⁄R]) ≃ₗ[A]
          Ω[((𝒱.pullback c A).cover (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))).A01⁄A])
      (eH0 : LinearMap.ker ((𝒱.kaehlerSections c).cechDiff.baseChange A) ≃ₗ[A]
          ((𝒱.pullback c A).kaehlerSections (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))).H0)
      (eH1 : ((A ⊗[R] Ω[(𝒱.cover c).A01⁄R]) ⧸ LinearMap.range ((𝒱.kaehlerSections c).cechDiff.baseChange A))
          ≃ₗ[A] ((𝒱.pullback c A).kaehlerSections (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))).H1),
      (∀ a ω, e0 (a ⊗ₜ[R] ω) = a • (Scheme.TwoAffineOpenCover.HomOver.baseChange 𝒱 c A).kaehlerMap0 ω) ∧
      (∀ a ω, e1 (a ⊗ₜ[R] ω) = a • (Scheme.TwoAffineOpenCover.HomOver.baseChange 𝒱 c A).kaehlerMap1 ω) ∧
      (∀ a ω, e01 (a ⊗ₜ[R] ω) = a • (Scheme.TwoAffineOpenCover.HomOver.baseChange 𝒱 c A).kaehlerMap01 ω) ∧
      (∀ x, ((eH0 x : _ × _)) = (e0 (TensorProduct.prodRight R A A _ _ x.1).1,
          e1 (TensorProduct.prodRight R A A _ _ x.1).2)) ∧
      (∀ y, eH1 (Submodule.Quotient.mk y) = Submodule.Quotient.mk (e01 y)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_baseChangeIsos_kaehlerSections.solution
