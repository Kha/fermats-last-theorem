import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import Definitions.Def_Dieudonne_FontaineHodge
import Definitions.Def_Dieudonne_UnipotentWittCovector
import Definitions.Def_Dieudonne_FontaineFunctor
import Definitions.Def_MvFormalGroup_BasicV2
import Definitions.Def_MvFormalGroup_EndRingV2
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_PointsV2
import P2M.Util
import P2M.Sol.S_Deformation_FontaineLift_existsUnique_sub_mem_and_wSeries_adicEval_eq_of_isUnit_linearPart

universe u v

theorem Deformation.FontaineLift.existsUnique_sub_mem_and_wSeries_adicEval_eq_of_isUnit_linearPart
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (d : ℕ)
    (a : Fin d → ℕ → MvPowerSeries (Fin d) 𝓞)
    (ha : ∀ i n, MvPowerSeries.constantCoeff (a i n) = 0)
    (hJ : IsUnit ((MvFormalGroup.linearPart fun i => a i 0).map
      (Ideal.Quotient.mk (Ideal.span {(p : 𝓞)}))))
    (h2 : p ≠ 2 ∨
      ((MvFormalGroup.linearPart fun i => a i 0).map (Ideal.Quotient.mk (Ideal.span {(p : 𝓞)})) = 1 ∧
        ∀ i j : Fin d, j ≤ i →
          MvFormalGroup.linearPart (fun i => a i 1) i j ∈ Ideal.span {(p : 𝓞)}))
    (g : Type v) [CommRing g] [Algebra 𝓞 g] (hpg : (p : g) ∈ nonZeroDivisors g)
    [IsAdicComplete (Ideal.span {(p : g)}) g]
    (x₀ : Fin d → g) (hx₀ : ∀ j, x₀ j ∈ (Ideal.span {(p : g)}).radical)
    (ξ : Fin d → Localization.Away (p : g))
    (hξ : ∀ i, ξ i - Deformation.PLoc.wSeries p
      (fun n => MvFormalGroup.adicEval (Ideal.span {(p : g)}) x₀ (a i n)) ∈ Deformation.PLoc.pSub p g) :
    ∃! x : Fin d → g, (∀ j, x j - x₀ j ∈ Ideal.span {(p : g)}) ∧
      ∀ i, Deformation.PLoc.wSeries p
        (fun n => MvFormalGroup.adicEval (Ideal.span {(p : g)}) x (a i n)) = ξ i := by p2m_exact_reverting @_root_.P2MW.S_Deformation_FontaineLift_existsUnique_sub_mem_and_wSeries_adicEval_eq_of_isUnit_linearPart.solution
