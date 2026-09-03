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
import P2M.Sol.S_LanglandsTunnell_RankinSelberg_forall_apply_iotaGL_mul_upperUnipotent3_mul_scalar_mul_eq_of_forall_apply_iotaGL_eq

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory
  LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker
  LanglandsTunnell.Converse LanglandsTunnell.CubicInduction
open scoped nonZeroDivisors

open scoped Classical

theorem LanglandsTunnell.RankinSelberg.forall_apply_iotaGL_mul_upperUnipotent3_mul_scalar_mul_eq_of_forall_apply_iotaGL_eq
    (p : HeightOneSpectrum (𝓞 ℚ))
    (W₁ W₂ : LocalGL3 p → ℂ)
    (hW₁ : IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ W₁)
    (hW₂ : IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ W₂)
    (f : ℕ)
    (hK₁ : ∀ k ∈ congruenceK1 (𝓞 ℚ) ℚ p f, ∀ g : LocalGL3 p, W₁ (g * k) = W₁ g)
    (hK₂ : ∀ k ∈ congruenceK1 (𝓞 ℚ) ℚ p f, ∀ g : LocalGL3 p, W₂ (g * k) = W₂ g)
    (ω : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (hω₁ : ∀ (t : (p.adicCompletion ℚ)ˣ) (h : LocalGL3 p),
      W₁ (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) = ((ω t : ℂˣ) : ℂ) * W₁ h)
    (hω₂ : ∀ (t : (p.adicCompletion ℚ)ˣ) (h : LocalGL3 p),
      W₂ (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) = ((ω t : ℂˣ) : ℂ) * W₂ h)
    (hι : ∀ h : GL (Fin 2) (p.adicCompletion ℚ), W₁ (iotaGL h) = W₂ (iotaGL h)) :
    ∀ (h : GL (Fin 2) (p.adicCompletion ℚ)) (x y z : p.adicCompletion ℚ) (t : (p.adicCompletion ℚ)ˣ) (k : LocalGL3 p),
      k ∈ congruenceK1 (𝓞 ℚ) ℚ p f →
        W₁ (iotaGL h * upperUnipotent3 x y z * Matrix.GeneralLinearGroup.scalar (Fin 3) t * k) =
          W₂ (iotaGL h * upperUnipotent3 x y z * Matrix.GeneralLinearGroup.scalar (Fin 3) t * k) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_RankinSelberg_forall_apply_iotaGL_mul_upperUnipotent3_mul_scalar_mul_eq_of_forall_apply_iotaGL_eq.solution
