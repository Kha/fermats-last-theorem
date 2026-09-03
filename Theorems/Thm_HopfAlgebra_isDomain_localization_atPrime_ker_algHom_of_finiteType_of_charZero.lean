import Mathlib
import P2M.Util
import P2M.Sol.S_HopfAlgebra_isDomain_localization_atPrime_ker_algHom_of_finiteType_of_charZero

theorem HopfAlgebra.isDomain_localization_atPrime_ker_algHom_of_finiteType_of_charZero
    (K : Type*) [Field K] [CharZero K]
    (A : Type*) [CommRing A] [HopfAlgebra K A] [Algebra.FiniteType K A]
    (χ : A →ₐ[K] K) :
    haveI : (RingHom.ker χ.toRingHom).IsPrime := RingHom.ker_isPrime χ.toRingHom
    IsDomain (Localization.AtPrime (RingHom.ker χ.toRingHom)) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_isDomain_localization_atPrime_ker_algHom_of_finiteType_of_charZero.solution
