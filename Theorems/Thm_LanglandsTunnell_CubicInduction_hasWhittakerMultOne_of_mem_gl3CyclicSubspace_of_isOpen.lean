import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_hasWhittakerMultOne_of_mem_gl3CyclicSubspace_of_isOpen
attribute [-simp] LanglandsTunnell.CubicInduction.translateRepStep_apply_coe LanglandsTunnell.CubicInduction.translateFn_apply LanglandsTunnell.CubicInduction.diagonal3_coe LanglandsTunnell.CubicInduction.halfModulus3_one LanglandsTunnell.CubicInduction.torusChar3_one

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.hasWhittakerMultOne_of_mem_gl3CyclicSubspace_of_isOpen
    (v : HeightOneSpectrum (𝓞 ℚ)) (ψv : AddChar (v.adicCompletion ℚ) ℂ) (hψv : Continuous ψv)
    (W : LocalGL3 v → ℂ)
    (hsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, W (g * k) = W g)
    (hmo : HasWhittakerMultOne ψv W)
    (W' : LocalGL3 v → ℂ) (hW' : W' ∈ gl3CyclicSubspace W) :
    HasWhittakerMultOne ψv W' := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_hasWhittakerMultOne_of_mem_gl3CyclicSubspace_of_isOpen.solution
