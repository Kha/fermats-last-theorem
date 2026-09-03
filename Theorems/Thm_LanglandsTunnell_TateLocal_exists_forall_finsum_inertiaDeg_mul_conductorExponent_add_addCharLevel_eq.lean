import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_DedekindDomain_Completion_BaseChange
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_TateLocal_exists_forall_finsum_inertiaDeg_mul_conductorExponent_add_addCharLevel_eq

open IsDedekindDomain NumberField LanglandsTunnell.TateLocal

theorem LanglandsTunnell.TateLocal.exists_forall_finsum_inertiaDeg_mul_conductorExponent_add_addCharLevel_eq
    (K : Type) [Field K] [NumberField K] (hdeg : Module.finrank ℚ K = 3) (w : HeightOneSpectrum (𝓞 ℚ)) :
    ∃ c₀ : ℕ, ∀ (χ : (w.adicCompletion ℚ)ˣ →* ℂˣ) (c : ℕ), c₀ ≤ c → HasConductorExponentAt ℚ w χ c →
      ∀ a : w.Extension (𝓞 K) → ℕ,
        (∀ P : w.Extension (𝓞 K),
          HasConductorExponentAt K P.1 (χ.comp (Units.map (Algebra.norm (w.adicCompletion ℚ)))) (a P)) →
        ∑ᶠ P : w.Extension (𝓞 K), (w.asIdeal.inertiaDeg' P.1.asIdeal : ℤ) *
            ((a P : ℤ) + LanglandsTunnell.TateLocal.addCharLevel (NumberField.StandardAddChar.psiLocal K P.1)) =
          3 * c := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_TateLocal_exists_forall_finsum_inertiaDeg_mul_conductorExponent_add_addCharLevel_eq.solution
