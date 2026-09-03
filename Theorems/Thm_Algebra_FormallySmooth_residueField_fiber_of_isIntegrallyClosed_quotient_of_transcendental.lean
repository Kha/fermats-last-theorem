import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_FormallySmooth_residueField_fiber_of_isIntegrallyClosed_quotient_of_transcendental

set_option autoImplicit false

theorem Algebra.FormallySmooth.residueField_fiber_of_isIntegrallyClosed_quotient_of_transcendental
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
    (π : O) (hπ : IsLocalRing.maximalIdeal O = Ideal.span {π})
    (halg : IsAlgClosed (IsLocalRing.ResidueField O))
    (A : Type) [CommRing A] [IsDomain A] [Algebra O A] [FaithfulSMul O A] [Algebra.FiniteType O A] [IsIntegrallyClosed A]

    (L : Type) [Field L] [Algebra O L] [IsFractionRing O L]
    (K : Type) [Field K] [Algebra L K] [Algebra O K] [IsScalarTower O L K] [Algebra A K] [IsScalarTower O A K]
    (hAK : Function.Injective (algebraMap A K))
    (x : A) (hx : Transcendental L (algebraMap A K x))
    (hfin : FiniteDimensional ↥(IntermediateField.adjoin L {algebraMap A K x}) K)

    (hdom : IsDomain (A ⧸ Ideal.span {algebraMap O A π}))
    (hnorm : IsIntegrallyClosed (A ⧸ Ideal.span {algebraMap O A π}))
    (hdim : Ring.KrullDimLE 1 (A ⧸ Ideal.span {algebraMap O A π})) :
    ∀ (𝔭 : Ideal O) [𝔭.IsPrime], Algebra.FormallySmooth 𝔭.ResidueField (𝔭.Fiber A) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_FormallySmooth_residueField_fiber_of_isIntegrallyClosed_quotient_of_transcendental.solution
