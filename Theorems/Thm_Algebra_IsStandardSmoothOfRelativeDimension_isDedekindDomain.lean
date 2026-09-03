import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_IsStandardSmoothOfRelativeDimension_isDedekindDomain

universe u v
theorem Algebra.IsStandardSmoothOfRelativeDimension.isDedekindDomain
    {k : Type u} {S : Type v} [Field k] [CommRing S] [IsDomain S] [Algebra k S]
    [Algebra.IsStandardSmoothOfRelativeDimension 1 k S] : IsDedekindDomain S := by p2m_exact_reverting @_root_.P2MW.S_Algebra_IsStandardSmoothOfRelativeDimension_isDedekindDomain.solution
