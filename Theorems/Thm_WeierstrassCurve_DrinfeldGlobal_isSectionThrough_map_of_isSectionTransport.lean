import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_LevelRelabelling
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_DrinfeldGlobal_isSectionThrough_map_of_isSectionTransport

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal ModularCurve.LevelRelabelling
open scoped Classical

attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassCurve.DrinfeldGlobal.isSectionThrough_map_of_isSectionTransport
    (A : Type) [CommRing A] (𝒢 : GroupLaws A) (q : ℕ) (𝒯 : LevelTransport A 𝒢 q) (h𝒯 : 𝒯.IsSectionTransport)
    {T T' : Type} [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T')
    (x : RawDrinfeldPair T)

    (hCO : ∃ (φ : projModelGradingCR x.curve →+*ᵍ projModelGradingCR (x.curve.map f.toRingHom))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (x.curve.map f.toRingHom)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR x.curve)).map φ),
        IsCoefficientHom x.curve f.toRingHom φ)
    (D : ModularCurve.LevelPData T)
    (hP : IsSectionThrough x.P D.xP D.yP) (hQ : IsSectionThrough x.Q D.xQ D.yQ) :
    IsSectionThrough (𝒯.map f x).P (f D.xP) (f D.yP) ∧ IsSectionThrough (𝒯.map f x).Q (f D.xQ) (f D.yQ) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_DrinfeldGlobal_isSectionThrough_map_of_isSectionTransport.solution
