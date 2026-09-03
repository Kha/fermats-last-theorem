import Definitions.Def_ModularCurve_NodeDescent
import Definitions.Def_ModularCurve_UVCrossingModel
import P2M.Util
import P2M.Sol.S_ModularCurve_UVCrossingModel_exists_prime_const_notMem_and_norm_sub_eq_eval_of_pow_eq_mul
attribute [-instance] AlgebraicClosure.Rat.isGalois
set_option autoImplicit false

universe u

open ModularCurve ModularCurve.UVCrossingModel IsLocalRing
open Valued in

theorem ModularCurve.UVCrossingModel.exists_prime_const_notMem_and_norm_sub_eq_eval_of_pow_eq_mul
    {A : ValuationSubring (AlgebraicClosure ℚ)} (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    [IsDiscreteValuationRing ↥(NodeLocalized.coeffSubring A K)]
    (ϖ : ↥(NodeLocalized.coeffSubring A K))
    {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (π : W) (hπ : Irreducible π) (E : ℕ) (hE : 1 ≤ E)
    (τ : AdicCompletion (maximalIdeal ↥(NodeLocalized.coeffSubring A K)) ↥(NodeLocalized.coeffSubring A K) ≃+* W)
    (hτϖ : τ (algebraMap ↥(NodeLocalized.coeffSubring A K) _ ϖ) = π)
    (j : AdicCompletion (maximalIdeal ↥(NodeLocalized.coeffSubring A K)) ↥(NodeLocalized.coeffSubring A K) →+*
      𝒪[(A.valuation).Completion])
    (hj : ∀ o : ↥(NodeLocalized.coeffSubring A K),
      ((j (algebraMap ↥(NodeLocalized.coeffSubring A K) _ o) : 𝒪[(A.valuation).Completion]) :
          (A.valuation).Completion) = ((o : AlgebraicClosure ℚ) : (A.valuation).Completion))
    (α : UVCrossingModel W (π ^ E)) (hα : IsUnit α)
    (c₀ : A) (hc₀ : c₀ ∈ maximalIdeal A)
    (hwin : ∃ m ∈ maximalIdeal A,
      (ϖ : AlgebraicClosure ℚ) ^ E = (c₀ : AlgebraicClosure ℚ) * (m : AlgebraicClosure ℚ))
    (g : Polynomial ↥(NodeLocalized.coeffSubring A K))
    (hg : (g.map (NodeLocalized.coeffSubring A K).subtype).eval (c₀ : AlgebraicClosure ℚ) = 0) :
    ∃ Q : PrimeSpectrum (UVCrossingModel W (π ^ E)),
      const (π ^ E) π ∉ Q.asIdeal ∧
      (g.map ((constHom (π ^ E)).comp (τ.toRingHom.comp
          (algebraMap ↥(NodeLocalized.coeffSubring A K)
            (AdicCompletion (maximalIdeal ↥(NodeLocalized.coeffSubring A K))
              ↥(NodeLocalized.coeffSubring A K)))))).eval (V (π ^ E) * α) ∈ Q.asIdeal ∧
      ∃ χ : Polynomial W,
        (∀ t : W, Algebra.norm W (Ideal.Quotient.mk Q.asIdeal (const (π ^ E) t - V (π ^ E) * α)) = χ.eval t) ∧
        χ.eval₂ ((𝒪[(A.valuation).Completion]).subtype.comp (j.comp τ.symm.toRingHom))
          ((c₀ : AlgebraicClosure ℚ) : (A.valuation).Completion) = 0 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_UVCrossingModel_exists_prime_const_notMem_and_norm_sub_eq_eval_of_pow_eq_mul.solution
