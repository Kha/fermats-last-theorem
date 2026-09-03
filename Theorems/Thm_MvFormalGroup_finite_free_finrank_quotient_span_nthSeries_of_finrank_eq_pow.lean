import Mathlib
import Definitions.Def_MvFormalGroup_BasicV2
import P2M.Util
import P2M.Sol.S_MvFormalGroup_finite_free_finrank_quotient_span_nthSeries_of_finrank_eq_pow
attribute [-instance] instTopologicallyFGOfFiniteType

open MvPowerSeries

universe u

theorem MvFormalGroup.finite_free_finrank_quotient_span_nthSeries_of_finrank_eq_pow
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [(Ideal.span {(p : 𝓞)}).IsMaximal] [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    {d : ℕ} (F : MvFormalGroup d 𝓞) (h v : ℕ)
    (hrk : Module.finrank (𝓞 ⧸ Ideal.span {(p : 𝓞)})
      (MvPowerSeries (Fin d) (𝓞 ⧸ Ideal.span {(p : 𝓞)}) ⧸
        Ideal.span (Set.range ((F.map (Ideal.Quotient.mk (Ideal.span {(p : 𝓞)}))).nthSeries (p ^ v)))) =
      p ^ (v * h)) :
    Module.Finite 𝓞 (MvPowerSeries (Fin d) 𝓞 ⧸ Ideal.span (Set.range (F.nthSeries (p ^ v)))) ∧
    Module.Free 𝓞 (MvPowerSeries (Fin d) 𝓞 ⧸ Ideal.span (Set.range (F.nthSeries (p ^ v)))) ∧
    Module.finrank 𝓞 (MvPowerSeries (Fin d) 𝓞 ⧸ Ideal.span (Set.range (F.nthSeries (p ^ v)))) =
      p ^ (v * h) := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_finite_free_finrank_quotient_span_nthSeries_of_finrank_eq_pow.solution
