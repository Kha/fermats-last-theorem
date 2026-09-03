import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_ValuationSubring_CompletionRatClosure
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_exists_adicBase_ratClosure

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CerednikDrinfeld CerednikDrinfeld.Omega ValuationSubring QuaternionAlgebra IsDedekindDomain

theorem CerednikDrinfeld.exists_adicBase_ratClosure
    (q : ℕ) [Fact q.Prime] (N : ℕ) (hqN : ¬ q ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (ϖ : Omega.PseudoUniformizer ↥(ratClosure A) A.valuation.Completion)
    (hϖ : algebraMap ↥(ratClosure A) A.valuation.Completion ϖ.ϖ = ((q : AlgebraicClosure ℚ) : A.valuation.Completion)) :
    ∃ (𝒪₀ : Type) (_ : CommRing 𝒪₀) (_ : IsDomain 𝒪₀) (_ : CharZero 𝒪₀) (_ : IsDiscreteValuationRing 𝒪₀)
      (π : 𝒪₀) (_ : Irreducible π) (_ : IsAdicComplete (Ideal.span {π}) 𝒪₀) (_ : Nat.card (𝒪₀ ⧸ Ideal.span {π}) = q)
      (_ : Ideal.span {((q : ℕ) : 𝒪₀)} = Ideal.span {π})
      (_ : Algebra 𝒪₀ ↥(ratClosure A)) (_ : IsFractionRing 𝒪₀ ↥(ratClosure A))
      (Onr : Type) (_ : CommRing Onr) (_ : IsDomain Onr) (_ : CharZero Onr) (_ : Algebra 𝒪₀ Onr) (Fr : Onr ≃ₐ[𝒪₀] Onr)
      (_ : IsAdicComplete (Ideal.span {algebraMap 𝒪₀ Onr π}) Onr)
      (_ : (Ideal.span {algebraMap 𝒪₀ Onr π}).IsMaximal)
      (_ : ∀ x : Onr, ∃ p : Polynomial 𝒪₀, p.Monic ∧ Polynomial.aeval x p ∈ Ideal.span {algebraMap 𝒪₀ Onr π})
      (_ : ∀ p : Polynomial Onr, p.Monic → 0 < p.natDegree → ∃ x : Onr, Polynomial.eval x p ∈ Ideal.span {algebraMap 𝒪₀ Onr π})
      (_ : ∀ x : Onr, Fr x - x ^ q ∈ Ideal.span {algebraMap 𝒪₀ Onr π})
      (vdet : Matrix.GeneralLinearGroup (Fin 2) ↥(ratClosure A) →* Multiplicative ℤ)
      (_ : ∀ (g : Matrix.GeneralLinearGroup (Fin 2) ↥(ratClosure A)) (n : ℤ), vdet g = Multiplicative.ofAdd n ↔
        ∃ u : 𝒪₀ˣ, (Matrix.GeneralLinearGroup.det g : ↥(ratClosure A)) = algebraMap 𝒪₀ ↥(ratClosure A) (u : 𝒪₀) * (algebraMap 𝒪₀ ↥(ratClosure A) π) ^ n)
      (ψ₀ : Onr →+* A.valuation.Completion),

      algebraMap 𝒪₀ ↥(ratClosure A) π = ϖ.ϖ ∧
      IsUnit ((N : ℕ) : 𝒪₀) ∧
      (∀ x : ↥(ratClosure A), x ∈ Set.range (algebraMap 𝒪₀ ↥(ratClosure A)) ↔
        Valued.v (algebraMap ↥(ratClosure A) A.valuation.Completion x) ≤ 1) ∧

      (∀ y : Onr, Valued.v (ψ₀ y) ≤ 1) ∧
      ψ₀.comp (algebraMap 𝒪₀ Onr) = (algebraMap ↥(ratClosure A) A.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ratClosure A)) ∧

      (∀ x y : A.valuation.Completion, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_exists_adicBase_ratClosure.solution
