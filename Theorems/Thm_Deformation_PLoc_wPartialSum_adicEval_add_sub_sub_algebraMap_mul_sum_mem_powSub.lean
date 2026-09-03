import Mathlib
import Definitions.Def_MvFormalGroup_BasicV2
import Definitions.Def_MvFormalGroup_PointsV2
import Definitions.Def_Dieudonne_FontaineFunctor
import P2M.Util
import P2M.Sol.S_Deformation_PLoc_wPartialSum_adicEval_add_sub_sub_algebraMap_mul_sum_mem_powSub

open MvPowerSeries

universe u v

theorem Deformation.PLoc.wPartialSum_adicEval_add_sub_sub_algebraMap_mul_sum_mem_powSub
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (d : ℕ)
    (a : Fin d → ℕ → MvPowerSeries (Fin d) 𝓞)
    (ha : ∀ i n, MvPowerSeries.constantCoeff (a i n) = 0)
    (Da : Fin d → ℕ → Fin d → MvPowerSeries (Fin d) 𝓞)
    (hDa : ∀ (i : Fin d) (n : ℕ) (j : Fin d) (m : Fin d →₀ ℕ),
      (Da i n j).coeff m = ((m j + 1 : ℕ) : 𝓞) * (a i n).coeff (m + Finsupp.single j 1))
    (g : Type v) [CommRing g] [Algebra 𝓞 g] [IsAdicComplete (Ideal.span {(p : g)}) g]
    (x : Fin d → g) (hx : ∀ j, x j ∈ (Ideal.span {(p : g)}).radical)
    (r : ℕ) (hr : 1 ≤ r) (h2 : p ≠ 2 ∨ 2 ≤ r) (y : Fin d → g) (i : Fin d) (N : ℕ) :
    Deformation.PLoc.wPartialSum p
        (fun n => MvFormalGroup.adicEval (Ideal.span {(p : g)}) (fun j => x j + (p : g) ^ r * y j) (a i n)) N
      - Deformation.PLoc.wPartialSum p
        (fun n => MvFormalGroup.adicEval (Ideal.span {(p : g)}) x (a i n)) N
      - algebraMap g (Localization.Away (p : g)) ((p : g) ^ r *
          ∑ j : Fin d, (∑ n ∈ Finset.range N,
            MvFormalGroup.adicEval (Ideal.span {(p : g)}) x (a i n) ^ (p ^ n - 1) *
              MvFormalGroup.adicEval (Ideal.span {(p : g)}) x (Da i n j)) * y j)
      ∈ Deformation.PLoc.powSub p g (r + 1) := by p2m_exact_reverting @_root_.P2MW.S_Deformation_PLoc_wPartialSum_adicEval_add_sub_sub_algebraMap_mul_sum_mem_powSub.solution
