import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_exists_ne_zero_forall_apply_principalSeries2Rep_eq_det_mul_of_ne_top_of_forall_sub_mem
attribute [-simp] AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.exists_ne_zero_forall_apply_principalSeries2Rep_eq_det_mul_of_ne_top_of_forall_sub_mem
    (p : HeightOneSpectrum (𝓞 ℚ)) (θ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ))
    (c : Fin 2 → ℕ)
    (hcθ : ∀ i : Fin 2, ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p (c i), θ i u = 1)
    (V : Submodule ℂ ↥(principalSeries2 p θ))
    (hV : ∀ (g : GL (Fin 2) (p.adicCompletion ℚ)), ∀ v ∈ V, principalSeries2Rep θ g v ∈ V)
    (hVtop : V ≠ ⊤)
    (hsl : ∀ (g : GL (Fin 2) (p.adicCompletion ℚ)), Matrix.GeneralLinearGroup.det g = 1 →
      ∀ f : ↥(principalSeries2 p θ), principalSeries2Rep θ g f - f ∈ V) :
    ∃ (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (lam : ↥(principalSeries2 p θ) →ₗ[ℂ] ℂ),
      lam ≠ 0 ∧ (∀ f ∈ V, lam f = 0) ∧
      ∀ (g : GL (Fin 2) (p.adicCompletion ℚ)) (f : ↥(principalSeries2 p θ)),
        lam (principalSeries2Rep θ g f) = ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * lam f := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_ne_zero_forall_apply_principalSeries2Rep_eq_det_mul_of_ne_top_of_forall_sub_mem.solution
