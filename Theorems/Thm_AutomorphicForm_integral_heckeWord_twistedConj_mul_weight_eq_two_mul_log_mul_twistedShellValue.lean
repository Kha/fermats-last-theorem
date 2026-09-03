import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_LocalWeightedOrbital
import Definitions.Def_AutomorphicForm_SatakeCombinationCoeff
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_LocalLanglands_HeckeCosetSystem
import P2M.Util
import P2M.Sol.S_AutomorphicForm_integral_heckeWord_twistedConj_mul_weight_eq_two_mul_log_mul_twistedShellValue

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open LanglandsTunnell.CubicInduction (diagUnits2)

theorem AutomorphicForm.integral_heckeWord_twistedConj_mul_weight_eq_two_mul_log_mul_twistedShellValue
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))
    (hw : Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
    (hprime : (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L)).Prime)
    (θ : w.1.adicCompletion L ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (hθ : orderOf θ = Module.finrank (v.adicCompletion K) (w.1.adicCompletion L))
    (hres : ∃ y : w.1.adicCompletion L, ‖y‖ ≤ 1 ∧ ‖θ y - y‖ = 1)

    (ϖ : w.1.adicCompletionIntegers L) (hϖ : Irreducible ϖ)
    (hϖ0 : algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) ϖ ≠ 0)
    (n : ℕ) (rL : Fin n → GL (Fin 2) (w.1.adicCompletion L))
    (hrL : HeckeIntegralSeam.IsHeckeCosetSystem
      (LocalGL2.integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L))
      (LocalGL2.diagPi ϖ hϖ0) rL)
    (z : GL (Fin 2) (w.1.adicCompletion L))
    (hz : (z : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) =
      algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) ϖ •
        (1 : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)))
    (k j : ℕ)

    (a b : (v.adicCompletion K)ˣ) (hab : a ≠ b)
    (α β : (w.1.adicCompletion L)ˣ)
    (hNα : ∏ i ∈ Finset.range (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L)), (θ ^ i) (α : w.1.adicCompletion L) =
      algebraMap (v.adicCompletion K) (w.1.adicCompletion L) a)
    (hNβ : ∏ i ∈ Finset.range (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L)), (θ ^ i) (β : w.1.adicCompletion L) =
      algebraMap (v.adicCompletion K) (w.1.adicCompletion L) b)
    (hT : AutomorphicForm.sigmaCentralizer (Matrix.GeneralLinearGroup.map θ.toAlgHom.toRingHom) (diagUnits2 α β) =
      (AutomorphicForm.localCentralizer K v (diagUnits2 a b)).map
        (Matrix.GeneralLinearGroup.map (algebraMap (v.adicCompletion K) (w.1.adicCompletion L))))
    (ra rb : ℤ) (hα : ‖(α : w.1.adicCompletion L)‖ = (Ideal.absNorm w.1.asIdeal : ℝ) ^ (-ra))
    (hβ : ‖(β : w.1.adicCompletion L)‖ = (Ideal.absNorm w.1.asIdeal : ℝ) ^ (-rb))
    (d : ℕ) (hd : ra = rb →
      ‖1 - ((b * a⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K)‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-(d : ℤ)))

    (τ' : @Measure (AutomorphicForm.sigmaCentralizer
        (Matrix.GeneralLinearGroup.map θ.toAlgHom.toRingHom) (diagUnits2 α β)) (borel _))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (borel _) τ')
    (hτ'1 : τ' {t | (t : GL (Fin 2) (w.1.adicCompletion L)) ∈ AutomorphicForm.localIntegralSet L w.1} = 1)
    (s : GL (Fin 2) (w.1.adicCompletion L) → ℝ) (hs0 : ∀ x, 0 ≤ s x)
    (hsm : Measurable[AutomorphicForm.localGLBorel L w.1] s) (hsc : HasCompactSupport s)
    (hs1 : ∀ x : GL (Fin 2) (w.1.adicCompletion L),
      (∑ ι : Fin k → Fin n, (AutomorphicForm.localIntegralSet L w.1).indicator (fun _ => (1 : ℂ))
          (((List.ofFn fun m => rL (ι m)).prod * z ^ j)⁻¹ *
            (x⁻¹ * diagUnits2 α β * Matrix.GeneralLinearGroup.map θ.toAlgHom.toRingHom x))) ≠ 0 →
        ∫ t : AutomorphicForm.sigmaCentralizer (Matrix.GeneralLinearGroup.map θ.toAlgHom.toRingHom)
            (diagUnits2 α β), s ((t : GL (Fin 2) (w.1.adicCompletion L)) * x) ∂τ' = 1)

    (WQ : ℕ → ℕ → ℕ) (hWQ00 : WQ 0 0 = 1) (hWQ0s : ∀ s : ℕ, WQ 0 (s + 1) = 0)
    (hWQroot : ∀ n : ℕ, WQ (n + 1) 0 = (Ideal.absNorm v.asIdeal ^ (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L)) + 1) * WQ n 1)
    (hWQstep : ∀ n s : ℕ, WQ (n + 1) (s + 1) = WQ n s + Ideal.absNorm v.asIdeal ^ (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L)) * WQ n (s + 2))
    (φ : ℤ → ℕ → ℂ)
    (hφ : ∀ (a : ℤ) (s : ℕ), φ a s = if 2 * a + s = (k : ℤ) + 2 * j then (WQ k s : ℂ) else 0)
    (P : ℕ → ℂ) (hP0 : P 0 = 1)
    (hP : ∀ i : ℕ, 1 ≤ i → i ≤ d →
      P i = ((Ideal.absNorm v.asIdeal : ℂ) ^ ((Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) - 1) * (i - 1)) * ∑ t ∈ Finset.range (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L)), (Ideal.absNorm v.asIdeal : ℂ) ^ t)⁻¹)
    (hPd : ∀ i : ℕ, d < i → P i = 0) :
    ∫ x : GL (Fin 2) (w.1.adicCompletion L),
        (∑ ι : Fin k → Fin n, (AutomorphicForm.localIntegralSet L w.1).indicator (fun _ => (1 : ℂ))
          (((List.ofFn fun m => rL (ι m)).prod * z ^ j)⁻¹ *
            (x⁻¹ * diagUnits2 α β * Matrix.GeneralLinearGroup.map θ.toAlgHom.toRingHom x))) *
          ((AutomorphicForm.LocalWeight.weight x : ℝ) : ℂ) * (s x : ℂ)
      ∂(AutomorphicForm.localHaar L w.1) =
      ((2 * Real.log (Ideal.absNorm v.asIdeal : ℝ) : ℝ) : ℂ) *
      (if ra + rb = (k : ℤ) + 2 * j then
        (if ra = rb then
          ∑ m ∈ Finset.Icc 1 (ra.toNat + d),
            (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) : ℂ) * m * ((Ideal.absNorm v.asIdeal : ℂ) ^ (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L))) ^ m * (1 - ((Ideal.absNorm v.asIdeal : ℂ) ^ (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L)))⁻¹) *
              (φ ra 0 * P m +
                ∑ i ∈ Finset.range (min d (m - 1) + 1),
                  (P i - P (i + 1)) * φ (ra - ((m - i : ℕ) : ℤ)) (2 * (m - i)))
        else
          ∑ m ∈ Finset.Icc 1 (min ra rb).toNat,
            (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) : ℂ) * m * ((Ideal.absNorm v.asIdeal : ℂ) ^ (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L))) ^ m * (1 - ((Ideal.absNorm v.asIdeal : ℂ) ^ (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L)))⁻¹) *
              φ (min ra rb - m) ((ra - rb).natAbs + 2 * m))
      else 0) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_integral_heckeWord_twistedConj_mul_weight_eq_two_mul_log_mul_twistedShellValue.solution
