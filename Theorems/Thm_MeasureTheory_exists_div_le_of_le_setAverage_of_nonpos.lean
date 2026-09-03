import Mathlib
import P2M.Util
import P2M.Sol.S_MeasureTheory_exists_div_le_of_le_setAverage_of_nonpos

theorem MeasureTheory.exists_div_le_of_le_setAverage_of_nonpos {α : Type*} [MeasurableSpace α]
    {μ : MeasureTheory.Measure α} {s E : Set α} {ψ : α → ℝ} {A θ : ℝ}
    (hsm : MeasurableSet s) (hψ : MeasureTheory.IntegrableOn ψ s μ) (hψ0 : ∀ x ∈ s, ψ x ≤ 0)
    (hE : E ⊆ s) (hs0 : μ s ≠ 0) (hs : μ s ≠ ⊤) (hθ : 0 < θ) (hθE : θ * μ.real s ≤ μ.real E)
    (hA : -A ≤ ⨍ x in s, ψ x ∂μ) :
    ∃ x ∈ E, -A / θ ≤ ψ x := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_exists_div_le_of_le_setAverage_of_nonpos.solution
