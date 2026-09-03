import Mathlib
import P2M.Util
namespace P2MW.S_IsDedekindDomain_exists_ne_zero_forall_isUnramifiedAt_of_notMem

set_option autoImplicit false

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

theorem solution
    (A B : Type*) [CommRing A] [IsDedekindDomain A] [CommRing B] [IsDedekindDomain B] [Algebra A B]
    [Module.IsTorsionFree A B] [Module.Finite A B] [Algebra.IsSeparable (FractionRing A) (FractionRing B)] :
    ∃ c : A, c ≠ 0 ∧ ∀ (P : Ideal B) [P.IsPrime], algebraMap A B c ∉ P → Algebra.IsUnramifiedAt A P := by
  classical
  have hD : differentIdeal A B ≠ ⊥ := differentIdeal_ne_bot
  haveI : Algebra.IsIntegral A B := inferInstance
  have hDc : (differentIdeal A B).comap (algebraMap A B) ≠ ⊥ := fun h => hD (Ideal.eq_bot_of_comap_eq_bot h)
  obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hDc
  refine ⟨c, hc0, fun P _ hcP => ?_⟩
  rw [← not_dvd_differentIdeal_iff]
  intro hdvd
  exact hcP ((Ideal.dvd_iff_le.mp hdvd) hc)
