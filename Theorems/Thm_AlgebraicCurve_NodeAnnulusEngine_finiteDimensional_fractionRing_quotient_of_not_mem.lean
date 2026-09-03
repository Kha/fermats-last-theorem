import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_NodeAnnulusEngine_finiteDimensional_fractionRing_quotient_of_not_mem

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem AlgebraicCurve.NodeAnnulusEngine.finiteDimensional_fractionRing_quotient_of_not_mem
    {L : Type*} [Field L] {F : Type*} [Field F] [Algebra L F] [IsCurveOver L F] [Algebra.EssFiniteType L F]
    (𝒩₀ : Subring F) [IsLocalRing ↥𝒩₀] [IsNoetherianRing ↥𝒩₀]
    (hgen : ∀ f : F, ∃ (n : ℕ) (c : Fin n → L) (a : Fin n → ↥𝒩₀) (b : ↥𝒩₀),
      (b : F) ≠ 0 ∧ f * (b : F) = ∑ i, c i • ((a i : ↥𝒩₀) : F))
    (C : Subring L) [IsDiscreteValuationRing ↥C]
    [Algebra ↥C ↥𝒩₀] (hCalg : ∀ c : ↥C, ((algebraMap ↥C ↥𝒩₀ c : ↥𝒩₀) : F) = algebraMap L F (c : L))
    (ϖ : ↥C) (hϖu : ¬ IsUnit ϖ) (hϖ0 : ϖ ≠ 0)
    (hld : ∀ (n : ℕ) (c : Fin n → L) (a : Fin n → ↥𝒩₀), LinearIndependent ↥C c →
      ∑ i, c i • ((a i : ↥𝒩₀) : F) = 0 → ∀ i, a i = 0)
    (𝔭 : Ideal ↥𝒩₀) [𝔭.IsPrime] (h𝔭0 : 𝔭 ≠ ⊥) (h𝔭ϖ : algebraMap ↥C ↥𝒩₀ ϖ ∉ 𝔭)
    (K κ : Type*) [Field K] [Field κ] [Algebra ↥C K] [IsFractionRing ↥C K]
    [Algebra (↥𝒩₀ ⧸ 𝔭) κ] [IsFractionRing (↥𝒩₀ ⧸ 𝔭) κ]
    [Algebra ↥C κ] [IsScalarTower ↥C (↥𝒩₀ ⧸ 𝔭) κ] [Algebra K κ] [IsScalarTower ↥C K κ] :
    FiniteDimensional K κ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_NodeAnnulusEngine_finiteDimensional_fractionRing_quotient_of_not_mem.solution
