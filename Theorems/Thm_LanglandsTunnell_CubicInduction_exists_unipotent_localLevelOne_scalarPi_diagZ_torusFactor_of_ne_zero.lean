import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_exists_unipotent_localLevelOne_scalarPi_diagZ_torusFactor_of_ne_zero

set_option autoImplicit false

open IsDedekindDomain NumberField UnramifiedWhittaker

theorem LanglandsTunnell.CubicInduction.exists_unipotent_localLevelOne_scalarPi_diagZ_torusFactor_of_ne_zero
    (v : HeightOneSpectrum (𝓞 ℚ)) (χ : AddChar (v.adicCompletion ℚ) ℂ)
    (hχ : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ 1 → χ x = 1)
    {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (z : ℂ) (hz : z ≠ 0) (N lam om : ℂ) :
    ∃ W₂ : GL (Fin 2) (v.adicCompletion ℚ) → ℂ,
      (∀ (x : v.adicCompletion ℚ) (g : GL (Fin 2) (v.adicCompletion ℚ)),
        W₂ (unipotent x * g) = χ x * W₂ g) ∧
      (∀ (k g : GL (Fin 2) (v.adicCompletion ℚ)),
        k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ → W₂ (g * k) = W₂ g) ∧
      W₂ 1 = 1 ∧
      (∀ g : GL (Fin 2) (v.adicCompletion ℚ),
        W₂ (g * scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) = z * W₂ g) ∧
      ∀ m : ℤ, W₂ (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ m) =
        torusFactor N lam om m := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_unipotent_localLevelOne_scalarPi_diagZ_torusFactor_of_ne_zero.solution
