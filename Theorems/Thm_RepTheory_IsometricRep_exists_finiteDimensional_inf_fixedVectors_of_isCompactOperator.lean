import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Definitions.Def_RepTheory_SmoothAdmissibleSchurCommutant
import P2M.Util
import P2M.Sol.S_RepTheory_IsometricRep_exists_finiteDimensional_inf_fixedVectors_of_isCompactOperator

set_option autoImplicit false

open FLT.SmoothAdmissibleSchurCommutant
open scoped InnerProductSpace

universe v w

theorem RepTheory.IsometricRep.exists_finiteDimensional_inf_fixedVectors_of_isCompactOperator
    {G : Type v} [Group G] [TopologicalSpace G]
    {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (ρ : G →* Module.End ℂ H) (hρ : ∀ (g : G) (x y : H), ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ)
    (T : H →L[ℂ] H) (hT : ∀ (g : G) (x : H), T (ρ g x) = ρ g (T x))
    (hTc : ∀ K : Subgroup G, IsCompact (K : Set G) → IsOpen (K : Set G) →
      IsCompactOperator (fun x : ↥(fixedVectors ρ K) => T x))
    (hTx : ∃ x : H, (∃ K : Subgroup G, IsCompact (K : Set G) ∧ IsOpen (K : Set G) ∧ x ∈ fixedVectors ρ K) ∧
      T x ≠ 0) :
    ∃ X : Submodule ℂ H, (∀ (g : G) (x : H), x ∈ X → ρ g x ∈ X) ∧
      (∀ K : Subgroup G, IsCompact (K : Set G) → IsOpen (K : Set G) →
        FiniteDimensional ℂ ↥(X ⊓ fixedVectors ρ K)) ∧
      ∃ K₀ : Subgroup G, IsCompact (K₀ : Set G) ∧ IsOpen (K₀ : Set G) ∧ X ⊓ fixedVectors ρ K₀ ≠ ⊥ := by p2m_exact_reverting @_root_.P2MW.S_RepTheory_IsometricRep_exists_finiteDimensional_inf_fixedVectors_of_isCompactOperator.solution
