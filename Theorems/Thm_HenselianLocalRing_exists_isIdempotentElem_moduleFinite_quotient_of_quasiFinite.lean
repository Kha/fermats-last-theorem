import Mathlib
import P2M.Util
import P2M.Sol.S_HenselianLocalRing_exists_isIdempotentElem_moduleFinite_quotient_of_quasiFinite

universe u v

theorem HenselianLocalRing.exists_isIdempotentElem_moduleFinite_quotient_of_quasiFinite
    {R : Type u} [CommRing R] [HenselianLocalRing R]
    {S : Type v} [CommRing S] [Algebra R S] [Algebra.FiniteType R S] [Algebra.QuasiFinite R S] :
    ∃ e : S, IsIdempotentElem e ∧
      Module.Finite R (S ⧸ Ideal.span ({1 - e} : Set S)) ∧
      ∀ 𝔮 : Ideal S, 𝔮.IsPrime → 𝔮.comap (algebraMap R S) = IsLocalRing.maximalIdeal R → e ∉ 𝔮 := by p2m_exact_reverting @_root_.P2MW.S_HenselianLocalRing_exists_isIdempotentElem_moduleFinite_quotient_of_quasiFinite.solution
