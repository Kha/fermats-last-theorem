import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_mem_gl3CyclicSubspace_twist_det

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.mem_gl3CyclicSubspace_twist_det
    (v : HeightOneSpectrum (𝓞 ℚ)) (χv : (v.adicCompletion ℚ)ˣ →* ℂˣ) (W : LocalGL3 v → ℂ) :
    (∀ W' ∈ gl3CyclicSubspace W,
        (fun x : LocalGL3 v => ((χv (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * W' x) ∈ gl3CyclicSubspace (fun x : LocalGL3 v => ((χv (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * W x)) ∧
    (∀ W'' ∈ gl3CyclicSubspace (fun x : LocalGL3 v => ((χv (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * W x),
        ∃ W' ∈ gl3CyclicSubspace W, W'' = (fun x : LocalGL3 v => ((χv (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * W' x)) ∧
    ((fun x : LocalGL3 v => ((χv (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * W x) = 0 ↔ W = 0) ∧
    (∀ U : Subgroup (LocalGL3 v), (∀ k ∈ U, χv (Matrix.GeneralLinearGroup.det k) = 1) →
      ∀ W' : LocalGL3 v → ℂ, (∀ k ∈ U, ∀ g : LocalGL3 v, W' (g * k) = W' g) →
        ∀ k ∈ U, ∀ g : LocalGL3 v, (fun x : LocalGL3 v => ((χv (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * W' x) (g * k) = (fun x : LocalGL3 v => ((χv (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * W' x) g) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_mem_gl3CyclicSubspace_twist_det.solution
