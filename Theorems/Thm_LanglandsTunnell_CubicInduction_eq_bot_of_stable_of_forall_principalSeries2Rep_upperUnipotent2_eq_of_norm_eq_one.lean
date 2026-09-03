import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_eq_bot_of_stable_of_forall_principalSeries2Rep_upperUnipotent2_eq_of_norm_eq_one

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.eq_bot_of_stable_of_forall_principalSeries2Rep_upperUnipotent2_eq_of_norm_eq_one
    (p : HeightOneSpectrum (𝓞 ℚ)) (θ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ))
    (hθu : ∀ (i : Fin 2) (z : (p.adicCompletion ℚ)ˣ), ‖((θ i z : ℂˣ) : ℂ)‖ = 1)
    (c : Fin 2 → ℕ)
    (hcθ : ∀ i : Fin 2, ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p (c i), θ i u = 1)
    (V : Submodule ℂ ↥(principalSeries2 p θ))
    (hV : ∀ (g : GL (Fin 2) (p.adicCompletion ℚ)), ∀ v ∈ V, principalSeries2Rep θ g v ∈ V)
    (hN : ∀ (x : p.adicCompletion ℚ), ∀ v ∈ V, principalSeries2Rep θ (upperUnipotent2 p x) v = v) :
    V = ⊥ := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_eq_bot_of_stable_of_forall_principalSeries2Rep_upperUnipotent2_eq_of_norm_eq_one.solution
