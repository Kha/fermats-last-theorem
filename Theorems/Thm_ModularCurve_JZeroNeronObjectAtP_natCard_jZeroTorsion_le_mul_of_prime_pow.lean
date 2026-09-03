import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_ModularCurve_JZeroNeronAtPData
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_ModularCurve_ToricMonodromyPart
import P2M.Util
import P2M.Sol.S_ModularCurve_JZeroNeronObjectAtP_natCard_jZeroTorsion_le_mul_of_prime_pow
attribute [-instance] GaloisRep.DeformationRingData.instIsLocalHom GaloisRep.DeformationRingData.instCommRing GaloisRep.DeformationRingData.instIsLocalRing GaloisRep.DeformationRingData.instIsNoetherianRing GaloisRep.DeformationRingData.instIsAdicComplete GaloisRep.DeformationRingData.instAlgebra
attribute [-simp] GaloisRep.DeformationRingData.mk.injEq GaloisRep.DeformationRingData.mk.sizeOf_spec

set_option autoImplicit false

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve IsLocalRing
  AlgebraicCurve ModularCurve.JZeroNeronObjectAtP

theorem ModularCurve.JZeroNeronObjectAtP.natCard_jZeroTorsion_le_mul_of_prime_pow
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A) (hΛ : Λ.IsJacobian)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (ℓ k : ℕ) (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p)
    (hdisp : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ x ∈ jZeroTorsion (N₀ * p) (ℓ ^ k), σ • x - x ∈ O.toricPts (ℓ ^ k)) :
    Nat.card ↥(jZeroTorsion (N₀ * p) (ℓ ^ k)) ≤
      Nat.card ↥(AddSubgroup.closure {y : JZero (N₀ * p) | ∃ σ ∈ A.inertiaSubgroupIn ℚ,
          ∃ x ∈ jZeroTorsion (N₀ * p) (ℓ ^ k), y = σ • x - x}) *
        Nat.card ↥(jZeroTorsion (N₀ * p) (ℓ ^ k) ⊓ inertiaInvariants A (N₀ * p)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_JZeroNeronObjectAtP_natCard_jZeroTorsion_le_mul_of_prime_pow.solution
