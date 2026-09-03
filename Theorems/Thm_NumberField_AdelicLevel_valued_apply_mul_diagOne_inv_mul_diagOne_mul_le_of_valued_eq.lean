import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import P2M.Util
import P2M.Sol.S_NumberField_AdelicLevel_valued_apply_mul_diagOne_inv_mul_diagOne_mul_le_of_valued_eq

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain AutomorphicForm

theorem NumberField.AdelicLevel.valued_apply_mul_diagOne_inv_mul_diagOne_mul_le_of_valued_eq
    (K : Type) [Field K] [NumberField K] (h κ : AdelicGL2 (𝓞 K) K) (hh : glFin (𝓞 K) K h = 1)
    (hκ : glFin (𝓞 K) K κ ∈ finiteIntegralGL2 (𝓞 K) K)
    (t₀ t₁ : (AdeleRing (𝓞 K) K)ˣ) (a₀ a₁ : HeightOneSpectrum (𝓞 K) → ℤ)
    (ht₀ : ∀ v : HeightOneSpectrum (𝓞 K), Valued.v (((t₀ : AdeleRing (𝓞 K) K)).2 v) =
      ((Multiplicative.ofAdd (a₀ v) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    (ht₁ : ∀ v : HeightOneSpectrum (𝓞 K), Valued.v (((t₁ : AdeleRing (𝓞 K) K)).2 v) =
      ((Multiplicative.ofAdd (a₁ v) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    (v : HeightOneSpectrum (𝓞 K)) (i j : Fin 2) :
    Valued.v (((((h * ((diagOne t₀)⁻¹ * (diagOne t₁ * κ)) : AdelicGL2 (𝓞 K) K) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j)).2 v) ≤
      ((Multiplicative.ofAdd (((a₀ v).natAbs + (a₁ v).natAbs : ℕ) : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) ∧
    Valued.v ((((((h * ((diagOne t₀)⁻¹ * (diagOne t₁ * κ)))⁻¹ : AdelicGL2 (𝓞 K) K) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j)).2 v) ≤
      ((Multiplicative.ofAdd (((a₀ v).natAbs + (a₁ v).natAbs : ℕ) : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdelicLevel_valued_apply_mul_diagOne_inv_mul_diagOne_mul_le_of_valued_eq.solution
