import Definitions.Def_GaloisRep_ResidualEquiv
import P2M.Util
import P2M.Sol.S_ResidualGaloisRep_isAbsolutelyIrreducible_iff_span_eq_top

open Module LinearMap
theorem ResidualGaloisRep.isAbsolutelyIrreducible_iff_span_eq_top
    {k : Type} [Field k] (ρ : ResidualGaloisRep k) :
    ρ.IsAbsolutelyIrreducible ↔ Submodule.span k (Set.range ⇑ρ.ρ) = ⊤ := by p2m_exact_reverting @_root_.P2MW.S_ResidualGaloisRep_isAbsolutelyIrreducible_iff_span_eq_top.solution
