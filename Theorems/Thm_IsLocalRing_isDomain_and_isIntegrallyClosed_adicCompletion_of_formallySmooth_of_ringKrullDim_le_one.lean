import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_isDomain_and_isIntegrallyClosed_adicCompletion_of_formallySmooth_of_ringKrullDim_le_one
attribute [-instance] AdicCompletion.instIsLocalRingMaximalIdeal

set_option autoImplicit false

theorem IsLocalRing.isDomain_and_isIntegrallyClosed_adicCompletion_of_formallySmooth_of_ringKrullDim_le_one
    {A₀ : Type} [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀] (q : A₀)
    (hA₀q : IsLocalRing.maximalIdeal A₀ = Ideal.span {q})
    (S : Type) [CommRing S] [IsLocalRing S] [IsNoetherianRing S] [Algebra A₀ S]
    [Algebra.EssFiniteType A₀ S] [Algebra.FormallySmooth A₀ S]
    (hq : IsUnit (algebraMap A₀ S q)) (hdim : ringKrullDim S ≤ 1) :
    IsDomain (AdicCompletion (IsLocalRing.maximalIdeal S) S) ∧
      IsIntegrallyClosed (AdicCompletion (IsLocalRing.maximalIdeal S) S) ∧
      algebraMap S (AdicCompletion (IsLocalRing.maximalIdeal S) S) (algebraMap A₀ S q) ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_isDomain_and_isIntegrallyClosed_adicCompletion_of_formallySmooth_of_ringKrullDim_le_one.solution
