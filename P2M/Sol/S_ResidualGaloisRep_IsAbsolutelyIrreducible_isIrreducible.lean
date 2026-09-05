import Definitions.Def_GaloisRep_Residual
import Theorems.Thm_ResidualGaloisRep_isAbsolutelyIrreducible_iff_span_eq_top
import Theorems.Thm_Representation_isIrreducible_of_span_range_eq_top
import Theorems.Thm_ResidualGaloisRep_isIrreducible_iff_representationIsIrreducible
import P2M.Util
namespace P2MW.S_ResidualGaloisRep_IsAbsolutelyIrreducible_isIrreducible

set_option autoImplicit false

theorem solution {k : Type} [Field k] {ρ : ResidualGaloisRep k}
    (h : ρ.IsAbsolutelyIrreducible) : ρ.IsIrreducible := by
  haveI : Nontrivial ρ.V := Module.nontrivial_of_finrank_eq_succ ρ.finrank_eq
  exact (ResidualGaloisRep.isIrreducible_iff_representationIsIrreducible ρ).mpr
    (Representation.isIrreducible_of_span_range_eq_top ρ.ρ
      ((ResidualGaloisRep.isAbsolutelyIrreducible_iff_span_eq_top ρ).mp h))

