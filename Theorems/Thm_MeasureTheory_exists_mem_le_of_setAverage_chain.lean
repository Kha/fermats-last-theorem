import Mathlib
import P2M.Util
import P2M.Sol.S_MeasureTheory_exists_mem_le_of_setAverage_chain

theorem MeasureTheory.exists_mem_le_of_setAverage_chain {α : Type*} [MeasurableSpace α]
    {μ : MeasureTheory.Measure α} {ψ : α → ℝ} {G : ℕ → Set α} {B : ℕ → α → Set α} {L : ℕ}
    {A₀ κ θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hκ : 0 ≤ κ)
    (hBm : ∀ l < L, ∀ p ∈ G l, MeasurableSet (B l p))
    (hB0 : ∀ l < L, ∀ p ∈ G l, μ (B l p) ≠ 0)
    (hBt : ∀ l < L, ∀ p ∈ G l, μ (B l p) ≠ ⊤)
    (hψ0 : ∀ l < L, ∀ p ∈ G l, ∀ x ∈ B l p, ψ x ≤ 0)
    (hint : ∀ l < L, ∀ p ∈ G l, MeasureTheory.IntegrableOn ψ (B l p) μ)
    (hsmv : ∀ l < L, ∀ p ∈ G l, ψ p - κ ≤ ⨍ x in B l p, ψ x ∂μ)
    (hovl : ∀ l < L, ∀ p ∈ G l, θ * μ.real (B l p) ≤ μ.real (B l p ∩ G (l + 1)))
    {p₀ : α} (hp₀ : p₀ ∈ G 0) (hA₀ : -A₀ ≤ ψ p₀) :
    ∀ l ≤ L, ∃ p ∈ G l, -((A₀ + l * κ) / θ ^ l) ≤ ψ p := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_exists_mem_le_of_setAverage_chain.solution
