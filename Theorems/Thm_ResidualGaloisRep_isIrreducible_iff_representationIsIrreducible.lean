import Definitions.Def_GaloisRep_Residual
import Mathlib.RepresentationTheory.Irreducible
import P2M.Util
import P2M.Sol.S_ResidualGaloisRep_isIrreducible_iff_representationIsIrreducible

theorem ResidualGaloisRep.isIrreducible_iff_representationIsIrreducible {k : Type} [Field k]
    (ρ : ResidualGaloisRep k) :
    ρ.IsIrreducible ↔ Representation.IsIrreducible ρ.ρ := by p2m_exact_reverting @_root_.P2MW.S_ResidualGaloisRep_isIrreducible_iff_representationIsIrreducible.solution
