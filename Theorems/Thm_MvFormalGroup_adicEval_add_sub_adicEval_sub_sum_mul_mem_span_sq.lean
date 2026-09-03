import Mathlib
import Definitions.Def_MvFormalGroup_BasicV2
import Definitions.Def_MvFormalGroup_PointsV2
import P2M.Util
import P2M.Sol.S_MvFormalGroup_adicEval_add_sub_adicEval_sub_sum_mul_mem_span_sq

open MvPowerSeries

universe u v

theorem MvFormalGroup.adicEval_add_sub_adicEval_sub_sum_mul_mem_span_sq
    {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S]
    (J : Ideal S) [IsAdicComplete J S] {d : ℕ}
    (f : MvPowerSeries (Fin d) R) (Df : Fin d → MvPowerSeries (Fin d) R)
    (hDf : ∀ (j : Fin d) (m : Fin d →₀ ℕ),
      (Df j).coeff m = ((m j + 1 : ℕ) : R) * f.coeff (m + Finsupp.single j 1))
    (x z : Fin d → S) (hx : ∀ s, x s ∈ J.radical) (hz : ∀ s, z s ∈ J.radical) :
    MvFormalGroup.adicEval J (x + z) f - MvFormalGroup.adicEval J x f
        - ∑ j, MvFormalGroup.adicEval J x (Df j) * z j ∈ (Ideal.span (Set.range z)) ^ 2 := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_adicEval_add_sub_adicEval_sub_sum_mul_mem_span_sq.solution
