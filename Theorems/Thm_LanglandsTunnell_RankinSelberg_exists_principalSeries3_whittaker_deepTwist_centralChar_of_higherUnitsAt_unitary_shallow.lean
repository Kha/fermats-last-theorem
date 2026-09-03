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
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_RankinSelberg_exists_principalSeries3_whittaker_deepTwist_centralChar_of_higherUnitsAt_unitary_shallow
attribute [-simp] LanglandsTunnell.CubicInduction.translateRepStep_apply_coe LanglandsTunnell.CubicInduction.translateFn_apply

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory
  LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker
  LanglandsTunnell.Converse LanglandsTunnell.CubicInduction
open scoped nonZeroDivisors

open scoped Classical in

open scoped Classical in

theorem LanglandsTunnell.RankinSelberg.exists_principalSeries3_whittaker_deepTwist_centralChar_of_higherUnitsAt_unitary_shallow
    (p : HeightOneSpectrum (𝓞 ℚ))
    (ω₃ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hω₃u : ∀ x : (p.adicCompletion ℚ)ˣ, ‖((ω₃ x : ℂˣ) : ℂ)‖ = 1)
    (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hχu : ∀ x : (p.adicCompletion ℚ)ˣ, ‖((χ x : ℂˣ) : ℂ)‖ = 1)
    (kp : ℕ) (hkp : LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ p χ kp)
    (d : ℕ) (hd : 0 < d) (hdk : d < kp)
    (hω₀ : ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p d, (ω₃ * (χ ^ 3)⁻¹) u = 1) :
    ∃ (lam : Fin 3 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (W2 : LocalGL3 p → ℂ),
      lam 0 * lam 1 * lam 2 = ω₃ ∧
      (∀ i : Fin 3, LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ p (lam i) kp) ∧
      (∀ (i : Fin 3) (x : (p.adicCompletion ℚ)ˣ), ‖((lam i x : ℂˣ) : ℂ)‖ = 1) ∧
      (∀ i : Fin 3, IsLocallyConstant (lam i)) ∧
      (∀ i : Fin 3, ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p d, (lam i * χ⁻¹) u = 1) ∧
      (∃ (Λ : ↥(principalSeries3 p lam) →ₗ[ℂ] ℂ) (f : ↥(principalSeries3 p lam)),
        IsWhittakerFunctional3 (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ Λ ∧ W2 = coefficientFn Λ f) ∧
      IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ W2 ∧
      (∃ Uv : Subgroup (LocalGL3 p), IsOpen (Uv : Set (LocalGL3 p)) ∧ ∀ k ∈ Uv, ∀ g : LocalGL3 p, W2 (g * k) = W2 g) ∧
      W2 ≠ 0 ∧
      (∀ (t : (p.adicCompletion ℚ)ˣ) (h : LocalGL3 p),
        W2 (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) = ((ω₃ t : ℂˣ) : ℂ) * W2 h) ∧
      (∃ W' ∈ gl3CyclicSubspace W2, W' ≠ 0 ∧
        ∀ k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p,
          (∀ i j : Fin 3, Valued.v ((k : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j -
              (1 : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(d : ℤ))) →
          ∀ g : LocalGL3 p,
            ((χ (Matrix.GeneralLinearGroup.det (g * k)) : ℂˣ) : ℂ)⁻¹ * W' (g * k) =
              ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ * W' g) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_RankinSelberg_exists_principalSeries3_whittaker_deepTwist_centralChar_of_higherUnitsAt_unitary_shallow.solution
