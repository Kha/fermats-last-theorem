import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import P2M.Util
import P2M.Sol.S_Rep_isZero_tateCohomology_ihom_of_isPGroup
attribute [-simp] Rep.coe_tateδneg2_apply

set_option autoImplicit false
universe u
open CategoryTheory Rep MonoidalCategory
theorem Rep.isZero_tateCohomology_ihom_of_isPGroup {P : Type} [Group P] [Fintype P] {p : ℕ} [Fact p.Prime]
    (hP : IsPGroup p P) (VA : Type) [AddCommGroup VA] [Module.Free ℤ VA] (ρA : Representation ℤ P VA)
    (VR : Type) [AddCommGroup VR] [NoZeroSMulDivisors ℤ VR] (ρR : Representation ℤ P VR)
    (h1 : CategoryTheory.Limits.IsZero ((Rep.of ρA).tateCohomology (-1)))
    (h2 : CategoryTheory.Limits.IsZero ((Rep.of ρA).tateCohomology (-2))) (q : ℤ) :
    CategoryTheory.Limits.IsZero (((ihom (Rep.of ρA)).obj (Rep.of ρR)).tateCohomology q) := by p2m_exact_reverting @_root_.P2MW.S_Rep_isZero_tateCohomology_ihom_of_isPGroup.solution
