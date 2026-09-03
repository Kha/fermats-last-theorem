import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpaceCechTwist
import P2M.Util
namespace P2MW.S_ProjSpaceCech_Twist_subsingleton_cohomology_of_lt

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

universe u

noncomputable section

open Finset Function

namespace ProjSpaceCech
p2m_export "ProjSpaceCech" "Twist.cochain_subsingleton_of_lt Twist.H"
p2m_open "ProjSpaceCech"

section Cohomology

variable (R : Type u) [CommRing R] (n : ℕ) (d : ℤ)

namespace Twist p2m_export "ProjSpaceCech.Twist" "d cochain_subsingleton_of_lt H" end Twist
p2m_open_scoped "ProjSpaceCech.Twist" in

theorem Twist.subsingleton_cohomology_of_lt {i : ℕ} (hi : n < i) :
    Subsingleton (Twist.H R n d i) := by
  rcases i with _ | j
  · exact absurd hi (Nat.not_lt_zero n)
  dsimp only [Twist.H]
  have hsub := Twist.cochain_subsingleton_of_lt R n d hi
  exact ⟨fun x y => Quotient.inductionOn₂' x y fun a b =>
    congrArg _ (Subtype.ext (hsub.elim a.1 b.1))⟩

end Cohomology

end ProjSpaceCech

theorem solution (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) {i : ℕ}
    (hi : n < i) : Subsingleton (ProjSpaceCech.Twist.H R n d i) :=
  ProjSpaceCech.Twist.subsingleton_cohomology_of_lt R n d hi

end
