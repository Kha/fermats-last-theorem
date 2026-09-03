import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_principalSeries2Rep_sub_mem_of_det_eq_one_of_forall_upperUnipotent2_sub_mem

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.principalSeries2Rep_sub_mem_of_det_eq_one_of_forall_upperUnipotent2_sub_mem
    (p : HeightOneSpectrum (𝓞 ℚ)) (θ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ))
    (V : Submodule ℂ ↥(principalSeries2 p θ))
    (hV : ∀ (g : GL (Fin 2) (p.adicCompletion ℚ)), ∀ v ∈ V, principalSeries2Rep θ g v ∈ V)
    (hq : ∀ (x : p.adicCompletion ℚ) (f : ↥(principalSeries2 p θ)), principalSeries2Rep θ (upperUnipotent2 p x) f - f ∈ V)
    (g : GL (Fin 2) (p.adicCompletion ℚ)) (hg : Matrix.GeneralLinearGroup.det g = 1)
    (f : ↥(principalSeries2 p θ)) :
    principalSeries2Rep θ g f - f ∈ V := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_principalSeries2Rep_sub_mem_of_det_eq_one_of_forall_upperUnipotent2_sub_mem.solution
