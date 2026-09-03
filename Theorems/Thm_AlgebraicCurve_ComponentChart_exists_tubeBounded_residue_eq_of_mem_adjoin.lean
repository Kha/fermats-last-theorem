import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableChartsComap
import Definitions.Def_AlgebraicCurve_AffinoidCentre
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_ComponentChart_exists_tubeBounded_residue_eq_of_mem_adjoin

set_option autoImplicit false

namespace AlgebraicCurve

open IsLocalRing

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
  {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

theorem ComponentChart.exists_tubeBounded_residue_eq_of_mem_adjoin
    (C : ComponentChart A F Fbar) (hrat : ∀ P ∈ C.dom, P.IsRational)
    {ι : Type*} (g : ι → F) (hg : ∀ i, g i ∈ C.integers) (hbd : ∀ i, C.tubeBounded (g i))
    (y : Fbar) (hy : y ∈ Algebra.adjoin (ResidueField A) (Set.range fun i => C.residue ⟨g i, hg i⟩)) :
    ∃ (f : F) (hf : f ∈ C.integers), C.tubeBounded f ∧ C.residue ⟨f, hf⟩ = y := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_ComponentChart_exists_tubeBounded_residue_eq_of_mem_adjoin.solution
