import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_AdelicLevel
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_lintegral_ite_bottomRow_maximalCompactHaar_eq_mul_lintegral_maximalCompactAtHaar_empty
attribute [-simp] AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel AutomorphicForm IsDedekindDomain
open scoped ENNReal NNReal Classical

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem AutomorphicForm.exists_lintegral_ite_bottomRow_maximalCompactHaar_eq_mul_lintegral_maximalCompactAtHaar_empty
    (K : Type) [Field K] [NumberField K] (S : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ) :
    ∃ κ : ℝ, 0 < κ ∧
      (∀ F : AdelicGL2 (𝓞 K) K → ℝ≥0∞, Measurable F →
        (∀ k k' : AdelicGL2 (𝓞 K) K, glArch (𝓞 K) K k' = 1 → F (k * k') = F k) →
        (∫⁻ k, (if (∀ v ∈ S, Valued.v (((((k : AdelicGL2 (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0).2 v) ≤
              Valued.v (((((k : AdelicGL2 (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v) * ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) then F k else 0) ∂(maximalCompactHaar K)) =
          ENNReal.ofReal κ * ∫⁻ k, F k ∂(maximalCompactAtHaar K ∅)) ∧
      (∀ F : AdelicGL2 (𝓞 K) K → ℂ,
        AEStronglyMeasurable (fun k : ↥(adelicMaximalCompact K) => F k) (maximalCompactHaar K) →
        AEStronglyMeasurable (fun k : ↥(maximalCompactAt K ∅) => F k) (maximalCompactAtHaar K ∅) →
        (∃ B : ℝ, ∀ k, ‖F k‖ ≤ B) →
        (∀ k k' : AdelicGL2 (𝓞 K) K, glArch (𝓞 K) K k' = 1 → F (k * k') = F k) →
        (∫ k, (if (∀ v ∈ S, Valued.v (((((k : AdelicGL2 (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0).2 v) ≤
              Valued.v (((((k : AdelicGL2 (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v) * ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) then F k else 0) ∂(maximalCompactHaar K)) =
          (κ : ℂ) * ∫ k, F k ∂(maximalCompactAtHaar K ∅)) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_lintegral_ite_bottomRow_maximalCompactHaar_eq_mul_lintegral_maximalCompactAtHaar_empty.solution
