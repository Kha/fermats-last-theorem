import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetWhittaker
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_isGL3PsiWhittakerFn_of_forall_isGL3PsiWhittakerFn_finsum_cpow_mul

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.CubicInduction

open scoped Classical

theorem LanglandsTunnell.CubicInduction.isGL3PsiWhittakerFn_of_forall_isGL3PsiWhittakerFn_finsum_cpow_mul
    (p : HeightOneSpectrum (𝓞 ℚ)) (ψ : AddChar (p.adicCompletion ℚ) ℂ)
    (E : ℤ → LocalGL3 p → ℂ)
    (hEfin : ∀ C : Set (LocalGL3 p), IsCompact C → {i : ℤ | ∃ g ∈ C, E i g ≠ 0}.Finite)
    (W : ℂ → LocalGL3 p → ℂ)
    (hW : ∀ (u : ℂ) (g : LocalGL3 p), W u g = ∑ᶠ i : ℤ, (Ideal.absNorm p.asIdeal : ℂ) ^ (-(i : ℂ) * u) * E i g)
    (hWlaw : ∀ u : ℂ, IsGL3PsiWhittakerFn ψ (W u)) :
    ∀ i : ℤ, IsGL3PsiWhittakerFn ψ (E i) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_isGL3PsiWhittakerFn_of_forall_isGL3PsiWhittakerFn_finsum_cpow_mul.solution
