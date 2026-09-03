import Definitions.Def_GaloisRep_Adic
import P2M.Util
import P2M.Sol.S_GaloisRepAdic_span_range_eq_top_of_residual_isAbsolutelyIrreducible

theorem GaloisRepAdic.span_range_eq_top_of_residual_isAbsolutelyIrreducible
    {A : Type} [CommRing A] [IsLocalRing A] (ρ : GaloisRepAdic A)
    (h : ρ.residual.IsAbsolutelyIrreducible) :
    Submodule.span A (Set.range ⇑ρ.ρ) = ⊤ := by p2m_exact_reverting @_root_.P2MW.S_GaloisRepAdic_span_range_eq_top_of_residual_isAbsolutelyIrreducible.solution
