import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.TateLocal

theorem LanglandsTunnell.CubicInduction.apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one
    (v : HeightOneSpectrum (𝓞 ℚ)) (ψv : AddChar (v.adicCompletion ℚ) ℂ) (_hψv : ψv ≠ 1)
    (T : (LocalGL3 v → ℂ) →ₗ[ℂ] ℂ)
    (_hleft : ∀ (x y z : v.adicCompletion ℚ) (φ : LocalGL3 v → ℂ), IsSchwartzBruhat φ →
      T (fun g => φ ((upperUnipotent3 x y z)⁻¹ * g)) = ψv (x + y) * T φ)
    (_hright : ∀ (x y z : v.adicCompletion ℚ) (φ : LocalGL3 v → ℂ), IsSchwartzBruhat φ →
      T (fun g => φ (g * upperUnipotent3 x y z)) = ψv (-(x + y)) * T φ)
    (φ : LocalGL3 v → ℂ) (_hφ : IsSchwartzBruhat φ) :
    T (fun g => φ (longWeyl3 * (transposeInv3 g)⁻¹ * longWeyl3⁻¹)) = T φ := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.solution
