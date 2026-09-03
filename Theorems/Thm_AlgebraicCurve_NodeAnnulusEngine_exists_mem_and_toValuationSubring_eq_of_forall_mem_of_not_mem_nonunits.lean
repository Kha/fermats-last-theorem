import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_IsCurveOver
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_NodeAnnulusEngine_exists_mem_and_toValuationSubring_eq_of_forall_mem_of_not_mem_nonunits
attribute [-simp] AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem AlgebraicCurve.NodeAnnulusEngine.exists_mem_and_toValuationSubring_eq_of_forall_mem_of_not_mem_nonunits
    {L : Type*} [Field L] [IsAlgClosed L] [CharZero L] (A : ValuationSubring L) {F : Type*} [Field F] [Algebra L F]
    [IsCurveOver L F] [Algebra.EssFiniteType L F]
    (S : Set (Place L F))
    (𝒩₀ : Subring F) [IsLocalRing ↥𝒩₀]
    (hS : ∀ P : Place L F, P ∈ S ↔
      (∀ f : F, f ∈ 𝒩₀ → f ∈ P.toValuationSubring) ∧
      (∀ f : ↥𝒩₀, ¬ IsUnit f → ∃ h : P.evalAt (f : F) ∈ A, (⟨_, h⟩ : ↥A) ∈ maximalIdeal ↥A))
    (C : Subring L) (hC : ∀ c : L, c ∈ C → c ∈ A)
    (hCmem : ∀ c : L, c ∈ C → algebraMap L F c ∈ 𝒩₀)
    (ϖ : ↥C)
    (hϖ : ∀ d : ↥C, IsLocalRing.residue A ⟨(d : L), hC d d.2⟩ = 0 ↔ ∃ d' : ↥C, d = ϖ * d')
    [IsDomain ↥C] [IsDiscreteValuationRing ↥C]
    (halg : ∀ a : L, a ∈ A → IsAlgebraic ↥C a)
    (huniq : ∀ V : ValuationSubring L, (∀ c : L, c ∈ C → c ∈ V) → ((ϖ : ↥C) : L) ∈ V.nonunits → V = A)
    (hϖ𝒩 : ¬ IsUnit (⟨algebraMap L F ((ϖ : ↥C) : L), hCmem ϖ ϖ.2⟩ : ↥𝒩₀))
    (O : ValuationSubring F) (hO : ∀ f : F, f ∈ 𝒩₀ → f ∈ O)
    (hϖO : algebraMap L F ((ϖ : ↥C) : L) ∉ O.nonunits) (hOtop : O ≠ ⊤) :
    ∃ P ∈ S, P.toValuationSubring = O := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_NodeAnnulusEngine_exists_mem_and_toValuationSubring_eq_of_forall_mem_of_not_mem_nonunits.solution
