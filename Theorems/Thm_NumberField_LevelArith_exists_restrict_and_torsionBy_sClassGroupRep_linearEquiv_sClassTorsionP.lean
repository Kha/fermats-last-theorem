import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_NumberField_SelmerRepModP
import P2M.Util
import P2M.Sol.S_NumberField_LevelArith_exists_restrict_and_torsionBy_sClassGroupRep_linearEquiv_sClassTorsionP

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory MonoidalCategory Module Limits groupCohomology ExtCitation NumberField.LevelArith IsDedekindDomain
open scoped Classical NumberField NumberField.LevelArith TensorProduct Pointwise

theorem NumberField.LevelArith.exists_restrict_and_torsionBy_sClassGroupRep_linearEquiv_sClassTorsionP
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes)
    (K L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥K] [FiniteDimensional ℚ ↥L]
    (hKL : K ≤ L) [Normal ↥K ↥(levelField K L hKL)] (hnorm : IsNormalLevel K L) :
    ∃ (τ : ↥K.fixingSubgroup →* (↥L ≃ₐ[ℚ] ↥L)) (_ : ∀ (γ : ↥K.fixingSubgroup) (y : ↥L), (γ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (y : AlgebraicClosure ℚ) = ((τ γ y : ↥L) : AlgebraicClosure ℚ))
      (e : ↥(Submodule.torsionBy ℤ (sClassGroupRep ↥L ↥L (S : Set Nat.Primes)) (p : ℤ)) ≃ₗ[ZMod p] sClassTorsionP K L hKL S p),
      ∀ (γ : ↥K.fixingSubgroup) (x x' : ↥(Submodule.torsionBy ℤ (sClassGroupRep ↥L ↥L (S : Set Nat.Primes)) (p : ℤ))) (c : ClassGroup (𝓞 ↥L)),
        (x : sClassGroupRep ↥L ↥L (S : Set Nat.Primes)) = Submodule.Quotient.mk (Additive.ofMul c) →
        (x' : sClassGroupRep ↥L ↥L (S : Set Nat.Primes)) = Submodule.Quotient.mk (Additive.ofMul (classGroupAut ℚ ↥L (τ γ) c)) →
          e x' = (sClassTorsionP K L hKL S p).ρ γ (e x) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_LevelArith_exists_restrict_and_torsionBy_sClassGroupRep_linearEquiv_sClassTorsionP.solution
