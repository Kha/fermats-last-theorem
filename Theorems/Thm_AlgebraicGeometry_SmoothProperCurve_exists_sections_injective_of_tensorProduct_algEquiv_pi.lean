import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_SmoothProperCurve_exists_sections_injective_of_tensorProduct_algEquiv_pi

universe u

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmoothProperCurve
  NeronModelInfra

theorem AlgebraicGeometry.SmoothProperCurve.exists_sections_injective_of_tensorProduct_algEquiv_pi
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (R₀ : Type u) [CommRing R₀] [Algebra R R₀]
    (B : Type u) [CommRing B] [Algebra R₀ B]
    (ι : Spec (CommRingCat.of B) ⟶ pullback c (specMap R R₀)) [IsClosedImmersion ι]
    (hι : ι ≫ baseChange R c R₀ = specMap R₀ B)
    (R' : Type u) [CommRing R'] [Algebra R R'] [Algebra R₀ R'] [IsScalarTower R R₀ R']
    (d : ℕ) (φ : (R' ⊗[R₀] B) ≃ₐ[R'] (Fin d → R')) :
    ∃ σ : Fin d → SchemeHomOver (𝟙 (Spec (CommRingCat.of R'))) (baseChange R c R'),
      ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R')),
        Function.Injective fun i => s ≫ (σ i).1 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_SmoothProperCurve_exists_sections_injective_of_tensorProduct_algEquiv_pi.solution
