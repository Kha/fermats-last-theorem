import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_Correspondence
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_CurveModel_sum_mul_eq_zero_of_sum_mul_eq_zero_of_dense_of_germ_eq

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicCurve

theorem AlgebraicCurve.CurveModel.sum_mul_eq_zero_of_sum_mul_eq_zero_of_dense_of_germ_eq
    {k : Type} [Field k] [IsAlgClosed k] {F : Type} [Field F] [Algebra k F]
    (𝔐 : AlgebraicCurve.CurveModel k F)
    {F' : Type} [Field F'] [Algebra k F']
    (φ₀ φ₁ : F →ₐ[k] F') (hφ₀ : φ₀.toRingHom.IsIntegral) (hφ₁ : φ₁.toRingHom.IsIntegral)
    (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y]
    (θ : X ⟶ 𝔐.C) (hθ : IsOpenMap θ.base)
    (d₀ d₁ : Y ⟶ X)
    (hdom₀ : d₀.base (genericPoint Y) = genericPoint X)
    (hdom₁ : d₁.base (genericPoint Y) = genericPoint X)
    (j : F →+* ↑X.functionField)
    (hpin : ∀ (z : F) (U : 𝔐.C.Opens) (hU : genericPoint 𝔐.C ∈ U) (hU' : genericPoint X ∈ θ ⁻¹ᵁ U)
      (sec : 𝔐.C.presheaf.obj (Opposite.op U)),
      (𝔐.C.presheaf.germ U (genericPoint 𝔐.C) hU).hom sec = 𝔐.ffEquiv z →
      (X.presheaf.germ (θ ⁻¹ᵁ U) (genericPoint X) hU').hom ((θ.app U).hom sec) = j z)
    (δ₀ δ₁ : ↑X.functionField →+* ↑Y.functionField)
    (hδ₀ : ∀ (U : X.Opens) (hU : genericPoint X ∈ U) (hU' : genericPoint Y ∈ d₀ ⁻¹ᵁ U) (sec : X.presheaf.obj (Opposite.op U)),
      δ₀ ((X.presheaf.germ U (genericPoint X) hU).hom sec) = (Y.presheaf.germ (d₀ ⁻¹ᵁ U) (genericPoint Y) hU').hom ((d₀.app U).hom sec))
    (hδ₁ : ∀ (U : X.Opens) (hU : genericPoint X ∈ U) (hU' : genericPoint Y ∈ d₁ ⁻¹ᵁ U) (sec : X.presheaf.obj (Opposite.op U)),
      δ₁ ((X.presheaf.germ U (genericPoint X) hU).hom sec) = (Y.presheaf.germ (d₁ ⁻¹ᵁ U) (genericPoint Y) hU').hom ((d₁.app U).hom sec))
    (Ω : Type) [Field Ω] (ι : k →+* Ω)
    (hD : Dense {y : ↥Y | ∃ (y' : Spec (CommRingCat.of Ω) ⟶ Y) (P : Place k F'),
      y'.base (IsLocalRing.closedPoint Ω) = y ∧
      y' ≫ d₀ ≫ θ = Spec.map (CommRingCat.ofHom ι) ≫ (𝔐.pointEquivPlace.symm (P.restrictAlong φ₀ hφ₀)).1 ∧
      y' ≫ d₁ ≫ θ = Spec.map (CommRingCat.ofHom ι) ≫ (𝔐.pointEquivPlace.symm (P.restrictAlong φ₁ hφ₁)).1}) :
    ∀ (n : ℕ) (x y : Fin n → F),
      (∑ i, φ₀ (x i) * φ₁ (y i)) = 0 → (∑ i, δ₀ (j (x i)) * δ₁ (j (y i))) = 0 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_CurveModel_sum_mul_eq_zero_of_sum_mul_eq_zero_of_dense_of_germ_eq.solution
