import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_DrinfeldGlobal_comap_torsionIdeal_eq_comap_ker_one

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel
  WeierstrassCurve.DrinfeldGlobal IsLocalRing HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassCurve.DrinfeldGlobal.comap_torsionIdeal_eq_comap_ker_one
    {T : Type u} [CommRing T] (W : WeierstrassCurve T) (G : RelativeGroupLaw T (projModelStrCR W)) (q : ℕ)
    {Y : Scheme.{u}} (γ : Y ⟶ projModelCR W) :
    (torsionIdeal G q).comap (γ ≫ toPullbackId) =
      (Scheme.Hom.ker (G.one (𝟙 _)).1).comap (γ ≫ G.schemeNsmul q) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_DrinfeldGlobal_comap_torsionIdeal_eq_comap_ker_one.solution
