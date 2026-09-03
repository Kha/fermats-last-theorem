import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_WhittakerBlock_casimir_archDeriv_and_comm
attribute [-simp] LanglandsTunnell.CubicInduction.WhittakerBlock.coe_archDerivₗ_apply

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm

theorem LanglandsTunnell.CubicInduction.WhittakerBlock.casimir_archDeriv_and_comm
    (H : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hH : WhittakerBlock.IsArchSmooth3 H) :
    (∀ i j : Fin 3,
      casimir1 (archDeriv i j H) = archDeriv i j (casimir1 H) ∧
        casimir2 (archDeriv i j H) = archDeriv i j (casimir2 H) ∧
          casimir3 (archDeriv i j H) = archDeriv i j (casimir3 H)) ∧
      casimir1 (casimir2 H) = casimir2 (casimir1 H) ∧
        casimir1 (casimir3 H) = casimir3 (casimir1 H) ∧
          casimir2 (casimir3 H) = casimir3 (casimir2 H) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_WhittakerBlock_casimir_archDeriv_and_comm.solution
