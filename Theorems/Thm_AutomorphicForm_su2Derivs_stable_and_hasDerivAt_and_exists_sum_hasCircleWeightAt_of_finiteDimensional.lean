import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import P2M.Util
import P2M.Sol.S_AutomorphicForm_su2Derivs_stable_and_hasDerivAt_and_exists_sum_hasCircleWeightAt_of_finiteDimensional

set_option autoImplicit false

open NumberField AutomorphicForm NumberField.InfinitePlace NumberField.InfinitePlace.Completion

theorem AutomorphicForm.su2Derivs_stable_and_hasDerivAt_and_exists_sum_hasCircleWeightAt_of_finiteDimensional
    (F : Type) [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsComplex)
    (Y : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) [FiniteDimensional ℂ Y]
    (hYs : ∀ y ∈ Y, IsArchSmoothAtComplex hw y)
    (hYK : ∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ y ∈ Y,
      (fun g => y (g * rowIsometryInclAt₀ F w k)) ∈ Y) :
    let D₀ : (AdelicGL2 (𝓞 F) F → ℂ) → (AdelicGL2 (𝓞 F) F → ℂ) := fun y => archDerivAtComplex hw .iH y
    let D₁ : (AdelicGL2 (𝓞 F) F → ℂ) → (AdelicGL2 (𝓞 F) F → ℂ) :=
      fun y => archDerivAtComplex hw .Fm y - archDerivAtComplex hw .E y
    let D₂ : (AdelicGL2 (𝓞 F) F → ℂ) → (AdelicGL2 (𝓞 F) F → ℂ) :=
      fun y => archDerivAtComplex hw .iE y + archDerivAtComplex hw .iFm y
    let Mrot : ℝ → AdelicGL2 (𝓞 F) F := fun s => archFlowAtComplex hw .iH s
    let Rrot : ℝ → AdelicGL2 (𝓞 F) F := fun s => archComplexLiftAt hw
      !![(Real.cos s : ℂ), -(Real.sin s : ℂ); (Real.sin s : ℂ), (Real.cos s : ℂ)]
    let Srot : ℝ → AdelicGL2 (𝓞 F) F := fun s => archComplexLiftAt hw
      !![(Real.cos s : ℂ), (Real.sin s : ℂ) * Complex.I; (Real.sin s : ℂ) * Complex.I, (Real.cos s : ℂ)]
    (∀ y ∈ Y, D₀ y ∈ Y ∧ D₁ y ∈ Y ∧ D₂ y ∈ Y) ∧
    (∀ y ∈ Y, ∀ (g : AdelicGL2 (𝓞 F) F) (s : ℝ),
      HasDerivAt (fun t : ℝ => y (g * Mrot t)) (D₀ y (g * Mrot s)) s ∧
      HasDerivAt (fun t : ℝ => y (g * Rrot t)) (D₁ y (g * Rrot s)) s ∧
      HasDerivAt (fun t : ℝ => y (g * Srot t)) (D₂ y (g * Srot s)) s) ∧
    (∀ S : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ), S ≤ Y →
      (∀ y ∈ S, D₀ y ∈ S ∧ D₁ y ∈ S ∧ D₂ y ∈ S) →
      ∀ y ∈ S, ∀ s : ℝ, (fun g => y (g * Mrot s)) ∈ S ∧ (fun g => y (g * Rrot s)) ∈ S ∧
        (fun g => y (g * Srot s)) ∈ S) ∧
    (∀ y ∈ Y, ∃ (ms : Finset ℤ) (ys : ℤ → (AdelicGL2 (𝓞 F) F → ℂ)),
      (∀ m ∈ ms, ys m ∈ Y ∧ HasCircleWeightAt hw m (ys m) ∧ D₀ (ys m) = (Complex.I * (m : ℂ)) • ys m) ∧
      y = ∑ m ∈ ms, ys m) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_su2Derivs_stable_and_hasDerivAt_and_exists_sum_hasCircleWeightAt_of_finiteDimensional.solution
