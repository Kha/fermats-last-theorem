import Theorems.Thm_ResidualGaloisRep_isAbsolutelyIrreducible_iff_span_eq_top
import Theorems.Thm_Representation_span_range_baseChange_eq_top_iff
import Definitions.Def_GaloisRep_ResidualEquiv
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Algebra.Rat
import P2M.Util
namespace P2MW.S_ResidualGaloisRep_IsAbsolutelyIrreducible_baseChangeAlong

open Module LinearMap

theorem solution
    {k k' : Type} [Field k] [Field k'] {ρ : ResidualGaloisRep k}
    (hρ : ρ.IsAbsolutelyIrreducible) (φ : k →+* k') :
    (ρ.baseChangeAlong φ).IsAbsolutelyIrreducible := by
  letI : Algebra k k' := φ.toAlgebra
  have hspan := (ResidualGaloisRep.isAbsolutelyIrreducible_iff_span_eq_top ρ).mp hρ
  have h2 := (Representation.span_range_baseChange_eq_top_iff (K := k') ρ.ρ).mpr hspan
  exact (ResidualGaloisRep.isAbsolutelyIrreducible_iff_span_eq_top (ρ.baseChangeAlong φ)).mpr h2
