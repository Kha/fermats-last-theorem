import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_TateLocal_exists_finset_hasConductorExponentAt_le_eq_sum_of_forall_mem_higherUnitsAt

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem LanglandsTunnell.TateLocal.exists_finset_hasConductorExponentAt_le_eq_sum_of_forall_mem_higherUnitsAt
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (b : ℕ)
    (g : (v.adicCompletion K)ˣ → ℂ)
    (hg : ∀ u : (v.adicCompletion K)ˣ, Valued.v (u : v.adicCompletion K) = 1 →
      ∀ h ∈ LanglandsTunnell.TateLocal.higherUnitsAt K v b, g (u * h) = g u) :
    ∃ (S : Finset ((v.adicCompletion K)ˣ →* ℂˣ)) (c : ((v.adicCompletion K)ˣ →* ℂˣ) → ℂ),
      (∀ η ∈ S, ∃ m ≤ b, LanglandsTunnell.TateLocal.HasConductorExponentAt K v η m) ∧
      (∀ η ∈ S, ∀ x : (v.adicCompletion K)ˣ, ‖((η x : ℂˣ) : ℂ)‖ = 1) ∧
      ∀ u : (v.adicCompletion K)ˣ, Valued.v (u : v.adicCompletion K) = 1 →
        g u = ∑ η ∈ S, c η * ((η u : ℂˣ) : ℂ) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_TateLocal_exists_finset_hasConductorExponentAt_le_eq_sum_of_forall_mem_higherUnitsAt.solution
