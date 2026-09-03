import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_UVCrossingModel
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_NodeAnnulusEngine_isIntegral_and_evalAt_mem_of_mem_ends_of_forall_mem_toValuationSubring
attribute [-simp] AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.UVCrossingModel

theorem AlgebraicCurve.NodeAnnulusEngine.isIntegral_and_evalAt_mem_of_mem_ends_of_forall_mem_toValuationSubring
    {L : Type*} [Field L] [IsAlgClosed L] [CharZero L] (A : ValuationSubring L) {F : Type*} [Field F] [Algebra L F]
    [IsCurveOver L F] [Algebra.EssFiniteType L F]

    (S : Set (Place L F))
    (hrat : ∀ P ∈ S, P.IsRational)
    (𝒩₀ : Subring F) [IsLocalRing ↥𝒩₀] [IsNoetherianRing ↥𝒩₀]

    (hS : ∀ P : Place L F, P ∈ S ↔
      (∀ f : F, f ∈ 𝒩₀ → f ∈ P.toValuationSubring) ∧
      (∀ f : ↥𝒩₀, ¬ IsUnit f → ∃ h : P.evalAt (f : F) ∈ A, (⟨_, h⟩ : ↥A) ∈ maximalIdeal ↥A))

    (hgen : ∀ f : F, ∃ (n : ℕ) (c : Fin n → L) (a : Fin n → ↥𝒩₀) (b : ↥𝒩₀),
      (b : F) ≠ 0 ∧ f * (b : F) = ∑ i, c i • ((a i : ↥𝒩₀) : F))

    (C : Subring L) (hC : ∀ c : L, c ∈ C → c ∈ A)
    (hCmem : ∀ c : L, c ∈ C → algebraMap L F c ∈ 𝒩₀)
    (ϖ : ↥C)
    (hϖ : ∀ d : ↥C, IsLocalRing.residue A ⟨(d : L), hC d d.2⟩ = 0 ↔ ∃ d' : ↥C, d = ϖ * d')
    (hϖ0 : ((ϖ : ↥C) : L) ≠ 0)
    [IsDomain ↥C] [IsDiscreteValuationRing ↥C]
    (halg : ∀ a : L, a ∈ A → IsAlgebraic ↥C a)

    (hld : ∀ (n : ℕ) (c : Fin n → L) (a : Fin n → ↥𝒩₀), LinearIndependent ↥C c →
      ∑ i, c i • ((a i : ↥𝒩₀) : F) = 0 → ∀ i, a i = 0)
    (hrk : ∀ a b : ↥A, a ∈ maximalIdeal ↥A → b ≠ 0 → ∃ n : ℕ, b ∣ a ^ n)
    (hres : ∀ g : ↥𝒩₀, ∃ o : ↥C, ¬ IsUnit (g - ⟨algebraMap L F (o : L), hCmem o o.2⟩))

    {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (π : W) (hπ : Irreducible π)
    (σ : W →+* AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀)
    (hσπ : σ π = algebraMap ↥𝒩₀ (AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀) ⟨algebraMap L F (ϖ : L), hCmem ϖ ϖ.2⟩)
    (E : ℕ) (hE : 1 ≤ E)
    (ι : AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀ ≃+* UVCrossingModel W (π ^ E))
    (hconst : ∀ o : W, ι (σ o) = const (π ^ E) o)

    (hκ : ∀ a : ↥A, ∃ c : ↥C, a - ⟨(c : L), hC c c.2⟩ ∈ maximalIdeal ↥A)
    (huniq : ∀ V : ValuationSubring L, (∀ c : L, c ∈ C → c ∈ V) → ((ϖ : ↥C) : L) ∈ V.nonunits → V = A)

    (R₁ R₂ : ValuationSubring F)
    (h₁ : ∀ f : F, f ∈ 𝒩₀ → f ∈ R₁) (h₂ : ∀ f : F, f ∈ 𝒩₀ → f ∈ R₂)
    (hϖ₁ : algebraMap L F ((ϖ : ↥C) : L) ∈ R₁.nonunits) (hϖ₂ : algebraMap L F ((ϖ : ↥C) : L) ∈ R₂.nonunits)

    (x y : ↥𝒩₀) (γU γV : (UVCrossingModel W (π ^ E))ˣ)
    (hιx : ι (algebraMap ↥𝒩₀ (AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀) x) =
      (γU : UVCrossingModel W (π ^ E)) * U (π ^ E))
    (hιy : ι (algebraMap ↥𝒩₀ (AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀) y) =
      (γV : UVCrossingModel W (π ^ E)) * V (π ^ E))
    (hx₁ : ((x : ↥𝒩₀) : F) ∉ R₁.nonunits) (hx₂ : ((x : ↥𝒩₀) : F) ∈ R₂.nonunits)
    (hy₁ : ((y : ↥𝒩₀) : F) ∈ R₁.nonunits) (hy₂ : ((y : ↥𝒩₀) : F) ∉ R₂.nonunits) :
    ∀ f : F, f ∈ R₁ → f ∈ R₂ → (∀ P ∈ S, f ∈ P.toValuationSubring) →
      IsIntegral ↥𝒩₀ f ∧ ∀ P ∈ S, P.evalAt f ∈ A := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_NodeAnnulusEngine_isIntegral_and_evalAt_mem_of_mem_ends_of_forall_mem_toValuationSubring.solution
