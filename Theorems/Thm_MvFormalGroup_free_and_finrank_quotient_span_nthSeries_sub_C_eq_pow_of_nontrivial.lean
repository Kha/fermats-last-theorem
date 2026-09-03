import Mathlib
import Definitions.Def_MvFormalGroup_BasicV2
import Definitions.Def_MvFormalGroup_EndRingV2
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_PointsV2
import P2M.Util
import P2M.Sol.S_MvFormalGroup_free_and_finrank_quotient_span_nthSeries_sub_C_eq_pow_of_nontrivial
attribute [-instance] instTopologicallyFGOfFiniteType

set_option autoImplicit false

open MvPowerSeries

universe u v

theorem MvFormalGroup.free_and_finrank_quotient_span_nthSeries_sub_C_eq_pow_of_nontrivial
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [(Ideal.span {(p : 𝓞)}).IsMaximal] [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    {d : ℕ} (Φ : MvFormalGroup d 𝓞) [Φ.IsComm] (h : ℕ)
    (hh : Module.finrank (𝓞 ⧸ Ideal.span {(p : 𝓞)})
      (MvPowerSeries (Fin d) (𝓞 ⧸ Ideal.span {(p : 𝓞)}) ⧸
        Ideal.span (Set.range ((Φ.map (Ideal.Quotient.mk (Ideal.span {(p : 𝓞)}))).nthSeries p))) =
      p ^ h)
    (E : Type v) [CommRing E] [Algebra 𝓞 E] [Module.Free 𝓞 E] [Module.Finite 𝓞 E] [Nontrivial E]
    (v : ℕ) (b : Fin d → E) (hb : ∀ i, b i ∈ (Ideal.span {(p : E)}).radical) :
    Module.Free E (MvPowerSeries (Fin d) E ⧸
        Ideal.span (Set.range fun i => (Φ.nthSeries (p ^ v) i).map (algebraMap 𝓞 E) - C (b i))) ∧
      Module.Finite E (MvPowerSeries (Fin d) E ⧸
        Ideal.span (Set.range fun i => (Φ.nthSeries (p ^ v) i).map (algebraMap 𝓞 E) - C (b i))) ∧
      Module.finrank E (MvPowerSeries (Fin d) E ⧸
        Ideal.span (Set.range fun i => (Φ.nthSeries (p ^ v) i).map (algebraMap 𝓞 E) - C (b i))) =
        p ^ (v * h) := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_free_and_finrank_quotient_span_nthSeries_sub_C_eq_pow_of_nontrivial.solution
