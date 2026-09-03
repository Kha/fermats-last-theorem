import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import P2M.Util
import P2M.Sol.S_groupCohomology_exists_restrict_mem_levelCoboundaries2_of_forall_pow_eq_one
attribute [-simp] groupCohomology.cochainsPullPush₁_apply groupCohomology.cochainsPullPush₂_apply groupCohomology.coe_levelCocycles₂Map groupCohomology.continuousH2Map_continuousH2π

set_option autoImplicit false
open CategoryTheory groupCohomology
theorem groupCohomology.exists_restrict_mem_levelCoboundaries2_of_forall_pow_eq_one
    {p : ℕ} [Fact p.Prime] {G : Type} [Group G]
    (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (T : ℕ → Subgroup G) (hT : ∀ N M : ℕ, 0 < N → N ∣ M → T M ≤ T N)
    (C : Set (Subgroup G)) (hC : ∀ S ∈ C, ∀ N : ℕ, 0 < N → S ⊓ T N ∈ C)
    (base : ∀ S ∈ C, ∀ a : S × S → Rep.trivial (ZMod p) S (ZMod p),
      a ∈ levelCocycles₂ (r.comp S.subtype) (Rep.trivial (ZMod p) S (ZMod p)) →
        ∃ (N : ℕ) (_ : 0 < N),
          (fun g : ↥(S ⊓ T N) × ↥(S ⊓ T N) =>
              a (Subgroup.inclusion inf_le_left g.1, Subgroup.inclusion inf_le_left g.2))
            ∈ levelCoboundaries₂ ((r.comp S.subtype).comp (Subgroup.inclusion (inf_le_left : S ⊓ T N ≤ S)))
                (Rep.trivial (ZMod p) ↥(S ⊓ T N) (ZMod p)))
    (S : Subgroup G) (hS : S ∈ C) (B : Rep.{0} (ZMod p) S) [FiniteDimensional (ZMod p) B]
    (hsm : ∀ b : B, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s : S, (r.comp S.subtype) s ∈ F.fixingSubgroup → B.ρ s b = b)
    (hP : ∀ s : S, ∃ n : ℕ, B.ρ (s ^ p ^ n) = 1)
    (b : S × S → B) (hb : b ∈ levelCocycles₂ (r.comp S.subtype) B) :
    ∃ (N : ℕ) (_ : 0 < N),
      (fun g : ↥(S ⊓ T N) × ↥(S ⊓ T N) =>
          b (Subgroup.inclusion inf_le_left g.1, Subgroup.inclusion inf_le_left g.2))
        ∈ levelCoboundaries₂ ((r.comp S.subtype).comp (Subgroup.inclusion (inf_le_left : S ⊓ T N ≤ S)))
            (Rep.res (Subgroup.inclusion (inf_le_left : S ⊓ T N ≤ S)) B) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_exists_restrict_mem_levelCoboundaries2_of_forall_pow_eq_one.solution
