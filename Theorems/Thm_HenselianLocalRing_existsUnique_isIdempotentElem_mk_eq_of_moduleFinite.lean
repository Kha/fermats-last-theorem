import Mathlib
import P2M.Util
import P2M.Sol.S_HenselianLocalRing_existsUnique_isIdempotentElem_mk_eq_of_moduleFinite

universe u v

theorem HenselianLocalRing.existsUnique_isIdempotentElem_mk_eq_of_moduleFinite
    {R : Type u} [CommRing R] [HenselianLocalRing R]
    {S : Type v} [CommRing S] [Algebra R S] [Module.Finite R S]
    (ē : S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S)) (hē : IsIdempotentElem ē) :
    ∃! e : S, IsIdempotentElem e ∧
      Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R S)) e = ē := by p2m_exact_reverting @_root_.P2MW.S_HenselianLocalRing_existsUnique_isIdempotentElem_mk_eq_of_moduleFinite.solution
