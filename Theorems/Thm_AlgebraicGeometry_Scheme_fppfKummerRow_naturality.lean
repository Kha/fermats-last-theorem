import Mathlib
import Definitions.Def_AlgebraicGeometry_FppfSiteCohomology
import Definitions.Def_AlgebraicGeometry_FppfCohomologyLES
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_fppfKummerRow_naturality

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

theorem AlgebraicGeometry.Scheme.fppfKummerRow_naturality
    (G : Sheaf (smallFppfTopology specInt) Ab.{1}) (n : ℤ)
    (hS : (ShortComplex.mk (kernel.ι (n • 𝟙 G)) (n • 𝟙 G) (kernel.condition (n • 𝟙 G))).ShortExact)
    (t : G ⟶ G) :
    ∃ w : (n • 𝟙 G) ≫ t = t ≫ (n • 𝟙 G),
      (∀ x : fppfCohomology specInt G 0,
        (FppfCohomologyLES.cohomologyδ hS 0 1 rfl :
            fppfCohomology specInt G 0 →+ fppfCohomology specInt (kernel (n • 𝟙 G)) 1)
          (fppfCohomologyMap specInt t 0 x) =
        fppfCohomologyMap specInt (kernel.map (n • 𝟙 G) (n • 𝟙 G) t t w) 1
          ((FppfCohomologyLES.cohomologyδ hS 0 1 rfl :
            fppfCohomology specInt G 0 →+ fppfCohomology specInt (kernel (n • 𝟙 G)) 1) x)) ∧
      (∀ y : fppfCohomology specInt (kernel (n • 𝟙 G)) 1,
        fppfCohomologyMap specInt (kernel.ι (n • 𝟙 G)) 1
            (fppfCohomologyMap specInt (kernel.map (n • 𝟙 G) (n • 𝟙 G) t t w) 1 y) =
          fppfCohomologyMap specInt t 1 (fppfCohomologyMap specInt (kernel.ι (n • 𝟙 G)) 1 y)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_fppfKummerRow_naturality.solution
