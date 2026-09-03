import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import P2M.Util
import P2M.Sol.S_WindowMultiplicity_exists_forall_finite_and_le_pow_mul_ncard_stripRows
attribute [-instance] NumberField.AdelicHaar.locallyCompactSpace_adeleRing NumberField.AdelicHaar.finite_residueField_adicCompletionIntegers NumberField.AdelicHaar.locallyCompactSpace_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_finiteAdeleRing NumberField.AdelicHaar.compactSpace_adicCompletionIntegers NumberField.AdelicHaar.t2Space_finiteAdeleRing NumberField.AdelicHaar.t2Space_matrix_adeleRing NumberField.AdelicHaar.t2Space_adeleRing NumberField.AdelicHaar.fact_isOpen_adicCompletionIntegers NumberField.AdelicHaar.t2Space_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_matrix_adeleRing NumberField.AdelicHaar.t2Space_infiniteAdeleRing NumberField.AdelicHaar.properSpace_adicCompletion
attribute [-simp] NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero AutomorphicForm.CarrierPins.mk.injEq AutomorphicForm.CarrierPins.mk.sizeOf_spec AutomorphicForm.unipotentGL2_zero AutomorphicForm.constantTerm_const AutomorphicForm.constantTerm_zero AutomorphicForm.unipotentGL2_coe

set_option autoImplicit false

open NumberField

theorem WindowMultiplicity.exists_forall_finite_and_le_pow_mul_ncard_stripRows (K : Type) [Field K]
    [NumberField K] (𝔞 : Ideal (𝓞 K)) (h𝔞 : 𝔞 ≠ ⊥) (𝔫 : Ideal (𝓞 K)) (h𝔫 : 𝔫 ≠ ⊥) (κ' : ℝ) (hκ' : 1 < κ')
    (G : Set ((w : InfinitePlace K) → Matrix (Fin 2) (Fin 2) w.Completion)) (hG : IsCompact G)
    (hdet : ∀ g ∈ G, ∀ w, (g w).det ≠ 0) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ r₀ : 𝓞 K × 𝓞 K,
      (r₀.1 ∈ 𝔞 ∧ r₀.2 ∈ 𝔞 ∧ Ideal.span {r₀.1, r₀.2} = 𝔞) → ∀ η : ℝ, 0 < η → η ≤ η₀ → ∀ g ∈ G,
        ({p : 𝓞 K × 𝓞 K | (p.1 ∈ 𝔞 ∧ p.2 ∈ 𝔞 ∧ Ideal.span {p.1, p.2} = 𝔞) ∧
            p.1 - r₀.1 ∈ 𝔫 * 𝔞 ∧ p.2 - r₀.2 ∈ 𝔫 * 𝔞 ∧
            ∀ w : InfinitePlace K,
            η ≤ ‖(g w).det‖ /
              (‖algebraMap K w.Completion (p.1 : K) * g w 0 0 + algebraMap K w.Completion (p.2 : K) * g w 1 0‖ ^ 2 +
                ‖algebraMap K w.Completion (p.1 : K) * g w 0 1 + algebraMap K w.Completion (p.2 : K) * g w 1 1‖ ^ 2) ∧
            ‖(g w).det‖ /
              (‖algebraMap K w.Completion (p.1 : K) * g w 0 0 + algebraMap K w.Completion (p.2 : K) * g w 1 0‖ ^ 2 +
                ‖algebraMap K w.Completion (p.1 : K) * g w 0 1 + algebraMap K w.Completion (p.2 : K) * g w 1 1‖ ^ 2) ≤
              κ' * η}).Finite ∧
        c₀ ≤ η ^ Module.finrank ℚ K *
          (({p : 𝓞 K × 𝓞 K | (p.1 ∈ 𝔞 ∧ p.2 ∈ 𝔞 ∧ Ideal.span {p.1, p.2} = 𝔞) ∧
            p.1 - r₀.1 ∈ 𝔫 * 𝔞 ∧ p.2 - r₀.2 ∈ 𝔫 * 𝔞 ∧
            ∀ w : InfinitePlace K,
            η ≤ ‖(g w).det‖ /
              (‖algebraMap K w.Completion (p.1 : K) * g w 0 0 + algebraMap K w.Completion (p.2 : K) * g w 1 0‖ ^ 2 +
                ‖algebraMap K w.Completion (p.1 : K) * g w 0 1 + algebraMap K w.Completion (p.2 : K) * g w 1 1‖ ^ 2) ∧
            ‖(g w).det‖ /
              (‖algebraMap K w.Completion (p.1 : K) * g w 0 0 + algebraMap K w.Completion (p.2 : K) * g w 1 0‖ ^ 2 +
                ‖algebraMap K w.Completion (p.1 : K) * g w 0 1 + algebraMap K w.Completion (p.2 : K) * g w 1 1‖ ^ 2) ≤
              κ' * η}).ncard : ℝ) := by p2m_exact_reverting @_root_.P2MW.S_WindowMultiplicity_exists_forall_finite_and_le_pow_mul_ncard_stripRows.solution
