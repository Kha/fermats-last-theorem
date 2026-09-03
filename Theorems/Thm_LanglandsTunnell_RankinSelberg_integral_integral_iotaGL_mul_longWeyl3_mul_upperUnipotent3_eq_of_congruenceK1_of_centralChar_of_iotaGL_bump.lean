import Definitions.Def_LanglandsTunnell_CubicInduction_CellBumps
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_LanglandsTunnell_LambdaSquared
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler

import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_RankinSelberg_integral_integral_iotaGL_mul_longWeyl3_mul_upperUnipotent3_eq_of_congruenceK1_of_centralChar_of_iotaGL_bump

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory
  LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker
  LanglandsTunnell.Converse LanglandsTunnell.CubicInduction
open scoped nonZeroDivisors

theorem LanglandsTunnell.RankinSelberg.integral_integral_iotaGL_mul_longWeyl3_mul_upperUnipotent3_eq_of_congruenceK1_of_centralChar_of_iotaGL_bump
    (p : HeightOneSpectrum (𝓞 ℚ)) (f : ℕ)
    (ω : (p.adicCompletion ℚ)ˣ →* ℂˣ)

    (W₀ : LocalGL3 p → ℂ)
    (hlaw : IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ W₀)
    (hK1 : ∀ k ∈ congruenceK1 (𝓞 ℚ) ℚ p f, ∀ g : LocalGL3 p, W₀ (g * k) = W₀ g)
    (hω : ∀ (t : (p.adicCompletion ℚ)ˣ) (h : LocalGL3 p),
      W₀ (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) = ((ω t : ℂˣ) : ℂ) * W₀ h)
    (hbK : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤, ∀ h : GL (Fin 2) (p.adicCompletion ℚ),
      W₀ (iotaGL (h * k)) = W₀ (iotaGL h))
    (hbsupp : ∀ h : GL (Fin 2) (p.adicCompletion ℚ), W₀ (iotaGL h) ≠ 0 →
      ∃ x : p.adicCompletion ℚ, ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤, h = unipotentGL2 x * k)
    (hb1 : W₀ (iotaGL 1) = 1)

    (W₀' : LocalGL3 p → ℂ)
    (hlaw' : IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ W₀')
    (hK1' : ∀ k ∈ congruenceK1 (𝓞 ℚ) ℚ p f, ∀ g : LocalGL3 p, W₀' (g * k) = W₀' g)
    (hω' : ∀ (t : (p.adicCompletion ℚ)ˣ) (h : LocalGL3 p),
      W₀' (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) = ((ω t : ℂˣ) : ℂ) * W₀' h)
    (hbK' : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤, ∀ h : GL (Fin 2) (p.adicCompletion ℚ),
      W₀' (iotaGL (h * k)) = W₀' (iotaGL h))
    (hbsupp' : ∀ h : GL (Fin 2) (p.adicCompletion ℚ), W₀' (iotaGL h) ≠ 0 →
      ∃ x : p.adicCompletion ℚ, ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤, h = unipotentGL2 x * k)
    (hb1' : W₀' (iotaGL 1) = 1)

    (φ φ₁ : p.adicCompletion ℚ → ℂ)
    (hsupp : ∀ u y : p.adicCompletion ℚ, φ u ≠ 0 → φ₁ y ≠ 0 →
      y ≠ 0 ∧ Valued.v y⁻¹ ≤ WithZero.exp (-(f : ℤ)) ∧ Valued.v (y⁻¹ * u) ≤ WithZero.exp (-(f : ℤ))) :
    letI := LanglandsTunnell.TateLocal.localBorel ℚ p
    ∀ g : GL (Fin 2) (p.adicCompletion ℚ),
      (∫ u, ∫ y, W₀ (iotaGL g * longWeyl3 * upperUnipotent3 u 0 y) * (φ u * φ₁ y)
          ∂(LanglandsTunnell.TateLocal.selfDualHaarAt ℚ p) ∂(LanglandsTunnell.TateLocal.selfDualHaarAt ℚ p)) =
      (∫ u, ∫ y, W₀' (iotaGL g * longWeyl3 * upperUnipotent3 u 0 y) * (φ u * φ₁ y)
          ∂(LanglandsTunnell.TateLocal.selfDualHaarAt ℚ p) ∂(LanglandsTunnell.TateLocal.selfDualHaarAt ℚ p)) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_RankinSelberg_integral_integral_iotaGL_mul_longWeyl3_mul_upperUnipotent3_eq_of_congruenceK1_of_centralChar_of_iotaGL_bump.solution
