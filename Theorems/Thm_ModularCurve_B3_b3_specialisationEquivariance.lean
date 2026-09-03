import Definitions.Def_ModularCurve_SpecialisationBridge
import P2M.Util
import P2M.Sol.S_ModularCurve_B3_b3_specialisationEquivariance

open ModularCurve ModularCurve.TatePoint ModularCurve.B3
theorem ModularCurve.B3.b3_specialisationEquivariance (p : ℕ) [Fact p.Prime] [NeZero p] (j₀ : Qbar) :
    ∃ β : CycSubH (nearCurve j₀) p ≃ CycSub (WeierstrassCurve.ofJ j₀) p,
      ∀ G G' : CycSubH (nearCurve j₀) p,
        (∃ m : HahnSeries.monodromy Qbar, b3Act j₀ m G.1 = G'.1) ↔
          SameOrbit (WeierstrassCurve.ofJ j₀) (β G).1 (β G').1 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_B3_b3_specialisationEquivariance.solution
