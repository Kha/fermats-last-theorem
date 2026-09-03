import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSupportedIn
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSum
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_SheafOfModules_Monoidal
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_ker_lift_and_supportedIn_of_finite_etale

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra MonoidalCategory
  AlgebraicGeometry.SmoothProperCurve TensorProduct

theorem AlgebraicGeometry.RelEffCartierDiv.exists_I_eq_ker_lift_and_supportedIn_of_finite_etale
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsSeparated c]
    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    (A : Type u) [CommRing A] [Algebra R A] [Module.Finite R A] [Module.FaithfullyFlat R A]
    (B : Type u) [CommRing B] [Algebra R B] [Module.Finite R B] [Algebra.Etale R B]
    (d : ℕ) (φ : TensorProduct R A B ≃ₐ[A] (Fin d → A))
    (z : Spec (CommRingCat.of B) ⟶ C) [IsClosedImmersion z]
    (hz : z ≫ c = Spec.map (CommRingCat.ofHom (algebraMap R B)))
    (hzU : Set.range z.base ⊆ (U : Set C)) :
    ∃ Z : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of R))),
      Z.I = (pullback.lift z (Spec.map (CommRingCat.ofHom (algebraMap R B)))
        (by rw [Category.comp_id]; exact hz)).ker ∧ Z.SupportedIn U := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_ker_lift_and_supportedIn_of_finite_etale.solution
