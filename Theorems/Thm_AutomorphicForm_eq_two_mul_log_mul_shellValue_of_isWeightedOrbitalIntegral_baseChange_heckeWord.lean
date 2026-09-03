import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_LocalWeightedOrbital
import Definitions.Def_AutomorphicForm_SatakeCombinationCoeff
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_LocalLanglands_HeckeCosetSystem
import P2M.Util
import P2M.Sol.S_AutomorphicForm_eq_two_mul_log_mul_shellValue_of_isWeightedOrbitalIntegral_baseChange_heckeWord

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open LanglandsTunnell.CubicInduction (diagUnits2)

theorem AutomorphicForm.eq_two_mul_log_mul_shellValue_of_isWeightedOrbitalIntegral_baseChange_heckeWord
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K))
    (ws : ∀ u : HeightOneSpectrum (𝓞 K), u.Extension (𝓞 L))
    (hinert : v.asIdeal.inertiaDeg' (ws v).1.asIdeal = Module.finrank K L)
    (ϖK : v.adicCompletionIntegers K) (hϖK : Irreducible ϖK)
    (hϖK0 : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖK ≠ 0)
    (nK : ℕ) (rK : Fin nK → GL (Fin 2) (v.adicCompletion K))
    (hrK : HeckeIntegralSeam.IsHeckeCosetSystem
      (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K))
      (LocalGL2.diagPi ϖK hϖK0) rK)
    (zK : GL (Fin 2) (v.adicCompletion K))
    (hzK : (zK : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖK •
        (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)))
    (k j : ℕ)
    (a b : (v.adicCompletion K)ˣ) (hab : a ≠ b)
    (τ : @Measure (AutomorphicForm.localCentralizer K v (diagUnits2 a b))
      (AutomorphicForm.localCentralizerBorel K v (diagUnits2 a b)))
    (hτ : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v (diagUnits2 a b)) τ)
    (hτ1 : τ {t | (t : GL (Fin 2) (v.adicCompletion K)) ∈ AutomorphicForm.localIntegralSet K v} = 1)
    (J : ℂ)
    (hJ : AutomorphicForm.IsWeightedOrbitalIntegral K v (diagUnits2 a b) τ
      (fun x : GL (Fin 2) (v.adicCompletion K) =>
        ∑ e ∈ (AutomorphicForm.SatakeCombination.slotWord K L ws v k j).support,
          AutomorphicForm.SatakeCombination.slotCoeff K L ws v k j e *
            ∑ ι : Fin (e 0) → Fin nK,
              (AutomorphicForm.localIntegralSet K v).indicator (fun _ => (1 : ℂ))
                (((List.ofFn fun m => rK (ι m)).prod * zK ^ (e 1))⁻¹ * x))
      J)

    (ra rb : ℤ) (ha : ‖(a : v.adicCompletion K)‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-((Module.finrank K L : ℤ) * ra)))
    (hb : ‖(b : v.adicCompletion K)‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-((Module.finrank K L : ℤ) * rb)))
    (d : ℕ) (hd : ra = rb →
      ‖1 - ((b * a⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K)‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-(d : ℤ)))

    (Wq : ℕ → ℕ → ℕ) (hWq00 : Wq 0 0 = 1) (hWq0s : ∀ s : ℕ, Wq 0 (s + 1) = 0)
    (hWqroot : ∀ n : ℕ, Wq (n + 1) 0 = (Ideal.absNorm v.asIdeal + 1) * Wq n 1)
    (hWqstep : ∀ n s : ℕ, Wq (n + 1) (s + 1) = Wq n s + Ideal.absNorm v.asIdeal * Wq n (s + 2))
    (f : ℤ → ℕ → ℂ)
    (hf : ∀ (a : ℤ) (s : ℕ), f a s =
      ∑ e ∈ (AutomorphicForm.SatakeCombination.univWord (Module.finrank K L - 1) k j).support,
        (AutomorphicForm.SatakeCombination.univWord (Module.finrank K L - 1) k j).coeff e * (Ideal.absNorm v.asIdeal : ℂ) ^ (e 1) / (Ideal.absNorm v.asIdeal : ℂ) ^ (Module.finrank K L * j) *
          (if 2 * a + s = (e 0 : ℤ) + 2 * (e 1 : ℤ) then (Wq (e 0) s : ℂ) else 0)) :
    J = ((2 * Real.log (Ideal.absNorm v.asIdeal : ℝ) : ℝ) : ℂ) *
      (if ra + rb = (k : ℤ) + 2 * j then
        (if ra = rb then
          f ((Module.finrank K L : ℤ) * ra) 0 * ∑ s ∈ Finset.Icc 1 d, (s : ℂ) * (Ideal.absNorm v.asIdeal : ℂ) ^ s * (1 - (Ideal.absNorm v.asIdeal : ℂ)⁻¹) +
            ∑ i ∈ Finset.Icc 1 (Module.finrank K L * ra.toNat),
              ((d + i : ℕ) : ℂ) * (Ideal.absNorm v.asIdeal : ℂ) ^ (d + i) * (1 - (Ideal.absNorm v.asIdeal : ℂ)⁻¹) * f ((Module.finrank K L : ℤ) * ra - i) (2 * i)
        else
          ∑ i ∈ Finset.Icc 1 (Module.finrank K L * (min ra rb).toNat),
            (i : ℂ) * (Ideal.absNorm v.asIdeal : ℂ) ^ i * (1 - (Ideal.absNorm v.asIdeal : ℂ)⁻¹) *
              f ((Module.finrank K L : ℤ) * min ra rb - i) (Module.finrank K L * (ra - rb).natAbs + 2 * i))
      else 0) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_eq_two_mul_log_mul_shellValue_of_isWeightedOrbitalIntegral_baseChange_heckeWord.solution
