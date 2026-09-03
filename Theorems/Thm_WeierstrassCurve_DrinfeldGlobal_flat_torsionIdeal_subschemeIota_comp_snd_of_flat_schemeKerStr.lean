import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_DrinfeldGlobal_flat_torsionIdeal_subschemeIota_comp_snd_of_flat_schemeKerStr

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal NeronModelInfra

theorem WeierstrassCurve.DrinfeldGlobal.flat_torsionIdeal_subschemeIota_comp_snd_of_flat_schemeKerStr
    {T : Type u} [CommRing T] (W : WeierstrassCurve T)
    (G : RelativeGroupLaw T (projModelStrCR W)) (n : ℕ)
    (h : Flat (G.schemeKerStr n)) :
    Flat ((torsionIdeal G n).subschemeι ≫ pullback.snd (projModelStrCR W) (𝟙 (Spec (CommRingCat.of T)))) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_DrinfeldGlobal_flat_torsionIdeal_subschemeIota_comp_snd_of_flat_schemeKerStr.solution
