import Mathlib
import P2M.Util
import P2M.Sol.S_MulSemiringAction_exists_basis_extending_invariants_eq_zpow_smul_and_iff_mem_span_fixedPoints_of_pairing_of_continuous_cocycle

set_option autoImplicit false

theorem MulSemiringAction.exists_basis_extending_invariants_eq_zpow_smul_and_iff_mem_span_fixedPoints_of_pairing_of_continuous_cocycle
    {C : Type*} [Field C] [TopologicalSpace C] [IsTopologicalRing C]
    {G : Type*} [Monoid G] [TopologicalSpace G] [MulSemiringAction G C] (χ : G →* Cˣ)
    (hχ : ∀ k : ℤ, k ≠ 0 → ∀ c : C, (∀ σ : G, σ • c = (χ σ : C) ^ k * c) → c = 0)
    (hχG : ∀ σ τ : G, σ • (χ τ : C) = χ τ)
    (hχc : ∀ k : ℤ, Continuous fun σ : G => (χ σ : C) ^ k)
    (m : ℤ) (hm : m ≠ 0)
    (hH1 : ∀ c : G → C, Continuous c →
      (∀ σ τ : G, c (σ * τ) = c σ + (χ σ : C) ^ (-m) * σ • c τ) →
        ∃ b : C, ∀ σ : G, c σ = (χ σ : C) ^ (-m) * σ • b - b)
    {W : Type*} [AddCommGroup W] [Module C W] [FiniteDimensional C W] (ρ : G → W →+ W)
    (hρ : ∀ (σ : G) (c : C) (w : W), ρ σ (c • w) = (σ • c) • ρ σ w)
    (hρmul : ∀ (σ τ : G) (w : W), ρ (σ * τ) w = ρ σ (ρ τ w))
    (hρc : ∀ (f : W →ₗ[C] C) (w : W), Continuous fun σ : G => f (ρ σ w))
    {W' : Type*} [AddCommGroup W'] [Module C W'] (ρ' : G → W' →+ W')
    (hρ' : ∀ (σ : G) (c : C) (w' : W'), ρ' σ (c • w') = (σ • c) • ρ' σ w')
    (B : W →ₗ[C] W' →ₗ[C] C)
    (hB : ∀ (σ : G) (w : W) (w' : W'), B (ρ σ w) (ρ' σ w') = (χ σ : C) ^ m * σ • B w w')
    (hBr : ∀ w' : W', (∀ w : W, B w w' = 0) → w' = 0)
    {ι ι' : Type*} [Fintype ι] [Fintype ι']
    (v : ι → W) (hv : ∀ (σ : G) (i : ι), ρ σ (v i) = v i) (hvi : LinearIndependent C v)
    (v' : ι' → W') (hv' : ∀ (σ : G) (j : ι'), ρ' σ (v' j) = v' j)
    (hvi' : LinearIndependent C v')
    (hcard : Fintype.card ι + Fintype.card ι' = Module.finrank C W) :
    ∃ b : Module.Basis (ι ⊕ ι') C W,
      (∀ i, b (Sum.inl i) = v i) ∧
      (∀ (σ : G) (j : ι'), ρ σ (b (Sum.inr j)) = ((χ σ : C) ^ m) • b (Sum.inr j)) ∧
      (∀ j, B (b (Sum.inr j)) (v' j) = 1 ∧ ∀ j', j' ≠ j → B (b (Sum.inr j)) (v' j') = 0) ∧
      (∀ w : W, (∀ σ : G, ρ σ w = w) ↔
        w ∈ Submodule.span (FixedPoints.subfield G C) (Set.range v)) ∧
      (∀ w : W, (∀ σ : G, ρ σ w = ((χ σ : C) ^ m) • w) ↔
        w ∈ Submodule.span (FixedPoints.subfield G C) (Set.range fun j => b (Sum.inr j))) ∧
      (∀ w' : W', (∀ σ : G, ρ' σ w' = w') ↔
        w' ∈ Submodule.span (FixedPoints.subfield G C) (Set.range v')) ∧
      (∀ (k : ℤ) (w : W), k ≠ 0 → k ≠ m → (∀ σ : G, ρ σ w = ((χ σ : C) ^ k) • w) → w = 0) := by p2m_exact_reverting @_root_.P2MW.S_MulSemiringAction_exists_basis_extending_invariants_eq_zpow_smul_and_iff_mem_span_fixedPoints_of_pairing_of_continuous_cocycle.solution
