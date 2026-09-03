import Definitions.Def_ModularCurve_JZeroNeronPrimaryTorsionSheaf
import Definitions.Def_ModularCurve_MultiplicativeType
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ModularCurve_natCard_eisensteinPrimaryTorsionBar_quotient_eq_pow_alpha_of_multiplicativeTypeNat
attribute [-instance] instIsScalarTowerTensorProduct_definitions
attribute [-simp] closureCounit_apply genericFibreAlgHom_tmul tensorInclusion_closureComul coe_closureAntipode_apply tensorToGenericFibre_tmul tensorInclusion_tmul mem_flatClosure_iff

open ModularCurve

theorem ModularCurve.natCard_eisensteinPrimaryTorsionBar_quotient_eq_pow_alpha_of_multiplicativeTypeNat
    (p : ℕ) [Fact p.Prime] (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2) (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (S : JZeroNeronPrimaryTorsionSheaf p q A hA)
    (Aq : ValuationSubring (AlgebraicClosure ℚ)) (hAq : Aq.LiesOverPrime q) :
    ∀ m, ∀ n : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → ℕ,
      (∀ σ, ∀ ζ : AlgebraicClosure ℚ, ζ ^ (q ^ m) = 1 → σ ζ = ζ ^ n σ) →
    ∀ W : AddSubgroup (JZero p),
      W ≤ eisensteinPrimaryTorsionBar p q m →
      MultiplicativeTypeNat (Aq.inertiaSubgroupIn ℚ) n W →
      (∀ σ ∈ Aq.inertiaSubgroupIn ℚ, ∀ x ∈ eisensteinPrimaryTorsionBar p q m,
        σ • (x : JZero p) - x ∈ W) →
      Nat.card (↥(eisensteinPrimaryTorsionBar p q m) ⧸ W.addSubgroupOf (eisensteinPrimaryTorsionBar p q m))
        = q ^ (S.invPins.inv m).α := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_natCard_eisensteinPrimaryTorsionBar_quotient_eq_pow_alpha_of_multiplicativeTypeNat.solution
