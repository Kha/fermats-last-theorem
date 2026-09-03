import Mathlib
import P2M.Util
import P2M.Sol.S_MeasureTheory_measure_setOf_exists_mem_le_mul_of_forall_closedBall

open MeasureTheory Metric Set
open scoped ENNReal NNReal

theorem MeasureTheory.measure_setOf_exists_mem_le_mul_of_forall_closedBall
    {α β : Type*} [MetricSpace α] [SecondCountableTopology α] [MeasurableSpace α] [OpensMeasurableSpace α]
    [HasBesicovitchCovering α] {_ : MeasurableSpace β} (μ : Measure β) (ν : Measure α) [SFinite ν]
    [ν.OuterRegular] (P : β → α → Prop) (S : Set α) (K : ℝ≥0∞) (hK : K ≠ ⊤)
    (h : ∀ x ∈ S, ∃ δ > 0, ∀ ρ ∈ Set.Ioo 0 δ,
      μ {b | ∃ y ∈ Metric.closedBall x ρ, P b y} ≤ K * ν (Metric.closedBall x ρ)) :
    μ {b | ∃ x ∈ S, P b x} ≤ K * ν S := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_measure_setOf_exists_mem_le_mul_of_forall_closedBall.solution
