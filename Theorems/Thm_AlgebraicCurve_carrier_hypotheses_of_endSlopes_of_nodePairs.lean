import Mathlib
import Definitions.Def_AlgebraicCurve_GluedPic0
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_carrier_hypotheses_of_endSlopes_of_nodePairs

set_option autoImplicit false

open AlgebraicCurve
open Classical in

theorem AlgebraicCurve.carrier_hypotheses_of_endSlopes_of_nodePairs
    {k F : Type*} [Field k] [Field F] [Algebra k F]
    (S : Finset (Place k F × Place k F)) (hSne : S.Nonempty)
    (hS₁₂ : ∀ s ∈ S, ∃ t ∈ S, t.2 = s.1) (hS₂₁ : ∀ s ∈ S, ∃ t ∈ S, t.1 = s.2)
    (Fx : Place k F → Prop) (hFx : ∀ s ∈ S, Fx s.1 ∧ Fx s.2)
    (T₁ T₂ : Finset (Place k F)) (hT₁ : ∀ v ∈ T₁, ¬ Fx v) (hT₂ : ∀ v ∈ T₂, ¬ Fx v)
    (Ebar₁ Ebar₂ EE₁ EE₂ : Place k F → ℤ)
    (hEbar₁ : ∀ v, Ebar₁ v = if v ∈ T₁ then 1 else 0) (hEbar₂ : ∀ v, Ebar₂ v = if v ∈ T₂ then 1 else 0)
    (hEE₁ : ∀ v, 0 ≤ EE₁ v) (hEE₂ : ∀ v, 0 ≤ EE₂ v)
    (u₁ u₂ : F) (hu₁ : u₁ ≠ 0) (hu₂ : u₂ ≠ 0)
    (O1₁ : ∀ v, ¬ Fx v → (v.ord u₁ : ℤ) = EE₁ v - Ebar₁ v)
    (O1₂ : ∀ v, ¬ Fx v → (v.ord u₂ : ℤ) = EE₂ v - Ebar₂ v)
    (O2₁ : ∀ v, Fx v → (∀ s ∈ S, v ≠ s.1) → 0 ≤ v.ord u₁)
    (O2₂ : ∀ v, Fx v → (∀ s ∈ S, v ≠ s.2) → 0 ≤ v.ord u₂)
    (e : Place k F × Place k F → ℕ) (he : ∀ s ∈ S, 1 ≤ e s) (δ : ℚ)
    (A₁ : ∀ s ∈ S, δ ≤ (e s : ℚ) * ((s.1.ord u₁ : ℤ) : ℚ))
    (A₂ : ∀ s ∈ S, -((e s : ℚ) * ((s.2.ord u₂ : ℤ) : ℚ)) ≤ δ)
    (B : ∀ s ∈ S, δ = 0 → s.2.ord u₂ = 0 → s.1.ord u₁ = 0 ∧ ∃ c : k, s.1.HasValue u₁ c ∧ s.2.HasValue u₂ c)
    (hgp₁ : ∀ h : F, (∀ v, v ∉ T₁ → 0 ≤ v.ord h) → (∀ v ∈ T₁, -1 ≤ v.ord h) → (∀ w ∈ S.image Prod.fst, w.HasValue h 0) → h = 0)
    (hgp₂ : ∀ h : F, (∀ v, v ∉ T₂ → 0 ≤ v.ord h) → (∀ v ∈ T₂, -1 ≤ v.ord h) → ∃ c : k, h = algebraMap k F c) :
    (∀ v, v ∉ T₁ → 0 ≤ v.ord u₁) ∧ (∀ v ∈ T₁, -1 ≤ v.ord u₁) ∧
    (∀ v, v ∉ T₂ → 0 ≤ v.ord u₂) ∧ (∀ v ∈ T₂, -1 ≤ v.ord u₂) ∧
    (∀ s ∈ S, ∃ c : k, s.1.HasValue u₁ c ∧ s.2.HasValue u₂ c) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_carrier_hypotheses_of_endSlopes_of_nodePairs.solution
