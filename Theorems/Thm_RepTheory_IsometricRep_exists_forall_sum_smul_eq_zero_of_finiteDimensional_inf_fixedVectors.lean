import Mathlib.Analysis.InnerProductSpace.Basic
import Definitions.Def_RepTheory_SmoothAdmissibleSchurCommutant
import P2M.Util
import P2M.Sol.S_RepTheory_IsometricRep_exists_forall_sum_smul_eq_zero_of_finiteDimensional_inf_fixedVectors

set_option autoImplicit false

open FLT.SmoothAdmissibleSchurCommutant
open scoped InnerProductSpace

universe v w

theorem RepTheory.IsometricRep.exists_forall_sum_smul_eq_zero_of_finiteDimensional_inf_fixedVectors
    {G : Type v} [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G]
    {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (ρ : G →* Module.End ℂ H) (hρ : ∀ (g : G) (x y : H), ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ)
    (S : Set (H →L[ℂ] H)) (hS : ∀ s ∈ S, ∀ (g : G) (x : H), s (ρ g x) = ρ g (s x))
    (hirr : ∀ W : Submodule ℂ H, IsClosed (W : Set H) →
      (∀ (g : G) (x : H), x ∈ W → ρ g x ∈ W) → (∀ s ∈ S, ∀ x : H, x ∈ W → s x ∈ W) → W = ⊥ ∨ W = ⊤)
    (hX : ∃ X : Submodule ℂ H, (∀ (g : G) (x : H), x ∈ X → ρ g x ∈ X) ∧
      (∀ K : Subgroup G, IsCompact (K : Set G) → IsOpen (K : Set G) →
        FiniteDimensional ℂ ↥(X ⊓ fixedVectors ρ K)) ∧
      ∃ K₀ : Subgroup G, IsCompact (K₀ : Set G) ∧ IsOpen (K₀ : Set G) ∧ X ⊓ fixedVectors ρ K₀ ≠ ⊥) :
    ∃ (E : Type w) (_ : AddCommGroup E) (_ : Module ℂ E) (πE : G →* Module.End ℂ E),
      IsIrreducibleRep πE ∧ IsSmoothRep πE ∧ IsAdmissibleRep πE ∧
        ∀ K : Subgroup G, IsCompact (K : Set G) → IsOpen (K : Set G) →
          ∃ (d : ℕ) (e : Fin d → E), ∀ x : H, (∀ k ∈ K, ρ k x = x) → ∀ μ : G →₀ ℂ,
            (∀ j : Fin d, (μ.sum fun (h : G) (c : ℂ) => c • πE h (e j)) = 0) →
              (μ.sum fun (h : G) (c : ℂ) => c • ρ h x) = 0 := by p2m_exact_reverting @_root_.P2MW.S_RepTheory_IsometricRep_exists_forall_sum_smul_eq_zero_of_finiteDimensional_inf_fixedVectors.solution
