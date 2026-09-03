import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
import P2M.Util
import P2M.Sol.S_IntermediateField_exists_etale_padicInt_integers_of_inertia_le_fixingSubgroup

set_option autoImplicit false

theorem IntermediateField.exists_etale_padicInt_integers_of_inertia_le_fixingSubgroup
    (p : ℕ) [Fact p.Prime]
    (K : IntermediateField ℚ_[p] (AlgebraicClosure ℚ_[p])) (hK : FiniteDimensional ℚ_[p] K)
    (hKur : (padicIntegers p).inertiaSubgroupIn ℚ_[p] ≤ K.fixingSubgroup) :
    ∃ (B : Type) (_ : CommRing B) (_ : IsDomain B) (_ : Algebra ℤ_[p] B) (_ : Module.Finite ℤ_[p] B)
      (_ : Module.Free ℤ_[p] B) (_ : Algebra.Etale ℤ_[p] B)
      (_ : Algebra B (AlgebraicClosure ℚ_[p])) (_ : IsScalarTower ℤ_[p] B (AlgebraicClosure ℚ_[p])),
      (∀ σ : (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]),
        (∀ b : B, σ (algebraMap B (AlgebraicClosure ℚ_[p]) b) = algebraMap B (AlgebraicClosure ℚ_[p]) b) →
          σ ∈ K.fixingSubgroup) ∧
      (∀ x : AlgebraicClosure ℚ_[p], x ∈ K → (padicIntegers p).valuation x = 1 →
        ∃ b : B, IsUnit b ∧ algebraMap B (AlgebraicClosure ℚ_[p]) b = x) := by p2m_exact_reverting @_root_.P2MW.S_IntermediateField_exists_etale_padicInt_integers_of_inertia_le_fixingSubgroup.solution
