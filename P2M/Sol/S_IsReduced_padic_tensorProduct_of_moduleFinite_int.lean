import Mathlib
import P2M.Util
namespace P2MW.S_IsReduced_padic_tensorProduct_of_moduleFinite_int

set_option autoImplicit false

open scoped TensorProduct

namespace ReducedEngines

theorem isReduced_rat_tensorProduct (S : Type*) [CommRing S] [IsReduced S] :
    IsReduced (ℚ ⊗[ℤ] S) := by
  letI : Algebra S (ℚ ⊗[ℤ] S) := Algebra.TensorProduct.rightAlgebra
  haveI : Algebra.IsPushout ℤ S ℚ (ℚ ⊗[ℤ] S) :=
    Algebra.IsPushout.symm (TensorProduct.isPushout (R := ℤ) (S := ℚ) (T := S))
  haveI : IsLocalization (Algebra.algebraMapSubmonoid S (nonZeroDivisors ℤ)) (ℚ ⊗[ℤ] S) :=
    (Algebra.isLocalization_iff_isPushout (nonZeroDivisors ℤ) ℚ).mpr inferInstance
  exact isReduced_localizationPreserves (Algebra.algebraMapSubmonoid S (nonZeroDivisors ℤ)) (ℚ ⊗[ℤ] S)
    (inferInstance : IsReduced S)

theorem formallyUnramified_of_finiteDimensional_of_isReduced (K A : Type*) [Field K] [PerfectField K] [CommRing A]
    [Algebra K A] [FiniteDimensional K A] [IsReduced A] : Algebra.FormallyUnramified K A := by
  haveI : IsArtinianRing A := IsArtinianRing.of_finite K A
  let e := IsArtinianRing.equivPi A
  haveI : ∀ I : MaximalSpectrum A, Algebra.FormallyUnramified K (A ⧸ I.asIdeal) := fun I => by
    letI := Ideal.Quotient.field I.asIdeal
    haveI : Algebra.IsAlgebraic K (A ⧸ I.asIdeal) := Algebra.IsAlgebraic.of_finite K _
    exact Algebra.FormallyUnramified.of_isSeparable K (A ⧸ I.asIdeal)
  haveI : Algebra.FormallyUnramified K (∀ I : MaximalSpectrum A, A ⧸ I.asIdeal) :=
    (Algebra.FormallyUnramified.pi_iff _).mpr this
  exact Algebra.FormallyUnramified.of_equiv (e.restrictScalars K).symm

end ReducedEngines

theorem solution
    (S : Type*) [CommRing S] [Module.Finite ℤ S] [Module.Free ℤ S] [IsReduced S] (ℓ : ℕ) [Fact ℓ.Prime] :
    IsReduced (TensorProduct ℤ ℚ_[ℓ] S) := by
  haveI : IsReduced (ℚ ⊗[ℤ] S) := ReducedEngines.isReduced_rat_tensorProduct S
  haveI : Algebra.FormallyUnramified ℚ (ℚ ⊗[ℤ] S) :=
    ReducedEngines.formallyUnramified_of_finiteDimensional_of_isReduced ℚ (ℚ ⊗[ℤ] S)
  haveI : IsReduced (ℚ_[ℓ] ⊗[ℚ] (ℚ ⊗[ℤ] S)) :=
    Algebra.FormallyUnramified.isReduced_of_field ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] (ℚ ⊗[ℤ] S))
  let e : ℚ_[ℓ] ⊗[ℚ] (ℚ ⊗[ℤ] S) ≃ₐ[ℚ_[ℓ]] ℚ_[ℓ] ⊗[ℤ] S :=
    Algebra.TensorProduct.cancelBaseChange ℤ ℚ ℚ_[ℓ] ℚ_[ℓ] S
  exact isReduced_of_injective e.symm.toRingHom e.symm.injective
