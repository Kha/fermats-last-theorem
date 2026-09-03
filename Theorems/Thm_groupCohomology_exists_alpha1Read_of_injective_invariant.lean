import Mathlib
import Definitions.Def_GroupCohomology_RelationModule
import P2M.Util
import P2M.Sol.S_groupCohomology_exists_alpha1Read_of_injective_invariant
set_option autoImplicit false
open CategoryTheory groupCohomology

theorem groupCohomology.exists_alpha1Read_of_injective_invariant
    {G : Type} [Group G] [Finite G] (C : Rep ℤ G)
    (invG : ↥(groupCohomology C 2) →+ AddCircle (1 : ℚ)) (hinv : Function.Injective invG)
    (p : ℕ) [Fact p.Prime] (B : Rep ℤ G) [Fintype B] (hB : ∀ b : B, p • b = 0)
    (hX : (Rep.relationSeqInt B).ShortExact) :
    ∃ al : (Rep.relationModuleInt B ⟶ C) →+ (↥(groupCohomology B 1) →+ ZMod p),
      ∀ (φ : Rep.relationModuleInt B ⟶ C) (y : ↥(groupCohomology B 1)),
        invG ((groupCohomology.map (MonoidHom.id G) φ 2).hom ((groupCohomology.δ hX 1 2 rfl).hom y))
            = ((((al φ y).val : ℚ) / (p : ℚ) : ℚ) : AddCircle (1 : ℚ)) ∧
        (al φ y = 0 ↔ (groupCohomology.map (MonoidHom.id G) φ 2).hom ((groupCohomology.δ hX 1 2 rfl).hom y) = 0) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_exists_alpha1Read_of_injective_invariant.solution
