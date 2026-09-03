import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_cosetSum_isRightInvariant_and_isGL3PsiWhittakerFn

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField

theorem LanglandsTunnell.CubicInduction.cosetSum_isRightInvariant_and_isGL3PsiWhittakerFn
    (v : HeightOneSpectrum (𝓞 ℚ)) (ψv : AddChar (v.adicCompletion ℚ) ℂ) (U : Subgroup (LocalGL3 v)) (gen : LocalGL3 v)
    {ι : Type} [Fintype ι] (reps : ι → LocalGL3 v) (W : LocalGL3 v → ℂ) :
    (HeckeIntegralSeam.IsHeckeCosetSystem U gen reps → IsRightInvariant U W → IsRightInvariant U (cosetSum reps W)) ∧
    (IsGL3PsiWhittakerFn ψv W → IsGL3PsiWhittakerFn ψv (cosetSum reps W)) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_cosetSum_isRightInvariant_and_isGL3PsiWhittakerFn.solution
