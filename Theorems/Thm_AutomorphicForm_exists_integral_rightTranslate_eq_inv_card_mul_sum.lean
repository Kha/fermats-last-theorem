import Definitions.Def_AutomorphicForm_CuspidalConstituent
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_integral_rightTranslate_eq_inv_card_mul_sum

set_option autoImplicit false

open MeasureTheory NumberField AutomorphicForm AutomorphicForm.CuspidalConstituent
open scoped BigOperators

theorem AutomorphicForm.exists_integral_rightTranslate_eq_inv_card_mul_sum
    (F : Type) [Field F] [NumberField F]
    (U : Subgroup (AdelicGL2 (𝓞 F) F)) (hU : IsCompact (U : Set (AdelicGL2 (𝓞 F) F)))
    (O : Subgroup (AdelicGL2 (𝓞 F) F)) (hO : IsOpen (O : Set (AdelicGL2 (𝓞 F) F)))
    (hUO : U = O ⊓ finiteAdelicGL2Subgroup F)
    [MeasurableSpace U] [BorelSpace U] (μ : Measure U) [μ.IsHaarMeasure] [IsProbabilityMeasure μ]
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : ∀ x : AdelicGL2 (𝓞 F) F, ∀ u ∈ U, φ (x * u) = φ x)
    {g : AdelicGL2 (𝓞 F) F} (hg : g ∈ finiteAdelicGL2Subgroup F) :
    ∃ (n : ℕ) (reps : Fin n → AdelicGL2 (𝓞 F) F),
      (∀ i, ∃ u ∈ U, ∃ u' ∈ U, reps i = u * g * u') ∧
      (∀ x : AdelicGL2 (𝓞 F) F, (∃ u ∈ U, ∃ u' ∈ U, x = u * g * u') → ∃ i, ∃ u ∈ U, x = reps i * u) ∧
      (∀ i j, (reps i)⁻¹ * reps j ∈ U → i = j) ∧ 0 < n ∧
      ∀ x : AdelicGL2 (𝓞 F) F, ∫ u, φ (x * (u : AdelicGL2 (𝓞 F) F) * g) ∂μ = (n : ℂ)⁻¹ * ∑ i, φ (x * reps i) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_integral_rightTranslate_eq_inv_card_mul_sum.solution
