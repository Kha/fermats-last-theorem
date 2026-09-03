import Mathlib
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_SmoothProperCurve_exists_sections_injective_comp_fst_eq_comp_of_tensorProduct_algEquiv_pi

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmoothProperCurve TensorProduct NeronModelInfra

theorem AlgebraicGeometry.SmoothProperCurve.exists_sections_injective_comp_fst_eq_comp_of_tensorProduct_algEquiv_pi
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (R' : Type u) [CommRing R'] [Algebra R R'] [Nontrivial R']
    (B : Type u) [CommRing B] [Algebra R B] (d : ℕ) (φ : R' ⊗[R] B ≃ₐ[R'] (Fin d → R'))
    (z : Spec (CommRingCat.of B) ⟶ C) [Mono z] (hz : z ≫ c = Spec.map (CommRingCat.ofHom (algebraMap R B))) :
    ∃ σ : Fin d → SchemeHomOver (𝟙 (Spec (CommRingCat.of R'))) (SmoothProperCurve.baseChange R c R'),
      Function.Injective σ ∧
      ∀ m, ∃ y : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of B),
        (σ m).1 ≫ pullback.fst c (SmoothProperCurve.specMap R R') = y ≫ z := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_SmoothProperCurve_exists_sections_injective_comp_fst_eq_comp_of_tensorProduct_algEquiv_pi.solution
