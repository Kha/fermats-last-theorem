import Mathlib.RingTheory.Norm.Defs
import Definitions.Def_NumberField_AdelicHaar
import P2M.Util
import P2M.Sol.S_NumberField_InfiniteAdeleRing_exists_isHaarMeasure_lintegral_eq_setLIntegral_inv_abs_norm_mixedSpace

set_option autoImplicit false

open MeasureTheory NumberField NumberField.InfiniteAdeleRing NumberField.mixedEmbedding
open scoped Classical ENNReal

theorem NumberField.InfiniteAdeleRing.exists_isHaarMeasure_lintegral_eq_setLIntegral_inv_abs_norm_mixedSpace
    (n : Type) [Fintype n] [DecidableEq n] (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (GL n (InfiniteAdeleRing K))] [BorelSpace (GL n (InfiniteAdeleRing K))] :
    let U : Set (n → n → mixedSpace K) := {e | IsUnit (Matrix.of e)}
    let ρ : (n → n → mixedSpace K) → ℝ≥0∞ := fun e => ENNReal.ofReal |Algebra.norm ℝ (Matrix.of e)|⁻¹
    let Φ : GL n (InfiniteAdeleRing K) → (n → n → mixedSpace K) := fun g i j =>
      ringEquiv_mixedSpace K ((g : Matrix n n (InfiniteAdeleRing K)) i j)
    let Ψ : (n → n → mixedSpace K) → GL n (InfiniteAdeleRing K) := fun e =>
      if h : IsUnit (Matrix.of e) then (h.map (ringEquiv_mixedSpace K).symm.mapMatrix).unit else 1
    ContinuousOn ρ U ∧ (∀ e ∈ U, 0 < ρ e) ∧ (∀ g, Φ g ∈ U) ∧ (∀ g, Ψ (Φ g) = g) ∧
      ∃ μ : Measure (GL n (InfiniteAdeleRing K)), μ.IsHaarMeasure ∧ μ.Regular ∧
        ∀ f : GL n (InfiniteAdeleRing K) → ℝ≥0∞, Measurable f →
          ∫⁻ g, f g ∂μ = ∫⁻ e in U, f (Ψ e) * ρ e ∂volume := by p2m_exact_reverting @_root_.P2MW.S_NumberField_InfiniteAdeleRing_exists_isHaarMeasure_lintegral_eq_setLIntegral_inv_abs_norm_mixedSpace.solution
