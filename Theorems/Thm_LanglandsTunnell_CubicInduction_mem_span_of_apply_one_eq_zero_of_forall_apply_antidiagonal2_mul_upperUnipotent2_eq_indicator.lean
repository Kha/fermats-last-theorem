import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_mem_span_of_apply_one_eq_zero_of_forall_apply_antidiagonal2_mul_upperUnipotent2_eq_indicator
attribute [-simp] AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.mem_span_of_apply_one_eq_zero_of_forall_apply_antidiagonal2_mul_upperUnipotent2_eq_indicator
    (p : HeightOneSpectrum (𝓞 ℚ)) (θ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ))
    (φ : ℤ → p.adicCompletion ℚ → ↥(principalSeries2 p θ))
    (hφ1 : ∀ (n : ℤ) (t : p.adicCompletion ℚ), (φ n t : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) 1 = 0)
    (hφ : ∀ (n : ℤ) (t x : p.adicCompletion ℚ),
      (φ n t : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (antidiagonal2 p * upperUnipotent2 p x) =
        if Valued.v (x - t) ≤ WithZero.exp (-n) then 1 else 0)
    (f : ↥(principalSeries2 p θ)) (h1 : (f : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) 1 = 0) :
    f ∈ Submodule.span ℂ (Set.range fun nt : ℤ × p.adicCompletion ℚ => φ nt.1 nt.2) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_mem_span_of_apply_one_eq_zero_of_forall_apply_antidiagonal2_mul_upperUnipotent2_eq_indicator.solution
