import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_IsUnramifiedAt_isEtaleAt_of_ringKrullDim_le

universe u v

theorem Algebra.IsUnramifiedAt.isEtaleAt_of_ringKrullDim_le
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    (S : Type v) [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
    (q : Ideal S) [q.IsPrime] [Algebra.IsUnramifiedAt R q]
    (hdim : ringKrullDim (Localization.AtPrime (q.under R)) ≤ ringKrullDim (Localization.AtPrime q)) :
    Algebra.IsEtaleAt R q ∧ Module.Flat R (Localization.AtPrime q) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_IsUnramifiedAt_isEtaleAt_of_ringKrullDim_le.solution
