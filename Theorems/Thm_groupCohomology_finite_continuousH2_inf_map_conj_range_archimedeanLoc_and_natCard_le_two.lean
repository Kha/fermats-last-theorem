import Mathlib
import Definitions.Def_GaloisRep_ComplexConjugation
import Definitions.Def_GroupCohomology_ContinuousH2
import P2M.Util
import P2M.Sol.S_groupCohomology_finite_continuousH2_inf_map_conj_range_archimedeanLoc_and_natCard_le_two

set_option autoImplicit false
open CategoryTheory groupCohomology ExtCitation

theorem groupCohomology.finite_continuousH2_inf_map_conj_range_archimedeanLoc_and_natCard_le_two
    (U : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    Finite (continuousH2 (U ⊓ (archimedeanLoc.range.map (MulAut.conj g).toMonoidHom)).subtype
        (Rep.res (U ⊓ (archimedeanLoc.range.map (MulAut.conj g).toMonoidHom)).subtype
          (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)))) ∧
    Nat.card (continuousH2 (U ⊓ (archimedeanLoc.range.map (MulAut.conj g).toMonoidHom)).subtype
        (Rep.res (U ⊓ (archimedeanLoc.range.map (MulAut.conj g).toMonoidHom)).subtype
          (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)))) ≤ 2 ∧
    (g * complexConjugation * g⁻¹ ∉ U →
      Subsingleton (continuousH2 (U ⊓ (archimedeanLoc.range.map (MulAut.conj g).toMonoidHom)).subtype
        (Rep.res (U ⊓ (archimedeanLoc.range.map (MulAut.conj g).toMonoidHom)).subtype
          (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ))))) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_finite_continuousH2_inf_map_conj_range_archimedeanLoc_and_natCard_le_two.solution
