import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_GL2TwistedOrbitalTransforms
import P2M.Util
import P2M.Sol.S_AutomorphicForm_GL2Twisted_exists_pos_forall_integral_eq_mul_setIntegral_iwasawaChart

set_option autoImplicit false

open MeasureTheory AutomorphicForm AutomorphicForm.GL2Twisted

theorem AutomorphicForm.GL2Twisted.exists_pos_forall_integral_eq_mul_setIntegral_iwasawaChart
    (μ : @Measure (GL (Fin 2) ℂ) (glBorelOf ℂ)) (hμ : @Measure.IsHaarMeasure _ _ _ (glBorelOf ℂ) μ) :
    ∃ c : ℝ, 0 < c ∧ ∀ F : GL (Fin 2) ℂ → ℂ, Measurable[glBorelOf ℂ] F → Integrable F μ →
      IntegrableOn (fun q : (ℂ × ℂ) × (ℂ × ℂ) =>
          ((2 * Real.sin q.1.1.im * Real.cos q.1.1.im / (q.2.1.re * q.2.1.im) : ℝ) : ℂ) *
            F (if h : 0 < q.2.1.re ∧ 0 < q.2.1.im then
                twistedSplitElt (q.2.1.re ^ 2) (q.2.1.im ^ 2) (q.2.1.re * q.2.2) ⟨pow_pos h.1 2, pow_pos h.2 2⟩ *
                  unitaryElt q.1.1.re q.1.1.im q.1.2.re q.1.2.im
              else 1))
        (({α : ℂ | 0 < α.re ∧ α.re < Real.pi ∧ 0 < α.im ∧ α.im < Real.pi / 2} ×ˢ
            {α : ℂ | 0 < α.re ∧ α.re < 2 * Real.pi ∧ 0 < α.im ∧ α.im < 2 * Real.pi}) ×ˢ
          ({β : ℂ | 0 < β.re ∧ 0 < β.im} ×ˢ (Set.univ : Set ℂ))) volume ∧
      ∫ g, F g ∂μ = (c : ℂ) *
        ∫ q in (({α : ℂ | 0 < α.re ∧ α.re < Real.pi ∧ 0 < α.im ∧ α.im < Real.pi / 2} ×ˢ
            {α : ℂ | 0 < α.re ∧ α.re < 2 * Real.pi ∧ 0 < α.im ∧ α.im < 2 * Real.pi}) ×ˢ
          ({β : ℂ | 0 < β.re ∧ 0 < β.im} ×ˢ (Set.univ : Set ℂ))),
          ((2 * Real.sin q.1.1.im * Real.cos q.1.1.im / (q.2.1.re * q.2.1.im) : ℝ) : ℂ) *
            F (if h : 0 < q.2.1.re ∧ 0 < q.2.1.im then
                twistedSplitElt (q.2.1.re ^ 2) (q.2.1.im ^ 2) (q.2.1.re * q.2.2) ⟨pow_pos h.1 2, pow_pos h.2 2⟩ *
                  unitaryElt q.1.1.re q.1.1.im q.1.2.re q.1.2.im
              else 1) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_GL2Twisted_exists_pos_forall_integral_eq_mul_setIntegral_iwasawaChart.solution
