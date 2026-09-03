import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_ContinuousH2Map
import P2M.Util
import P2M.Sol.S_groupCohomology_exists_forall_restrict_comap_mem_levelCoboundaries2_of_finiteDimensional

set_option autoImplicit false
open groupCohomology
theorem groupCohomology.exists_forall_restrict_comap_mem_levelCoboundaries2_of_finiteDimensional
    {p : ℕ} [Fact p.Prime] {Γ : Type} [Group Γ]
    (r : Γ →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (T : ℕ → Subgroup Γ) (hT : ∀ N M : ℕ, 0 < N → N ∣ M → T M ≤ T N)
    (S : Subgroup Γ) (B : Rep.{0} (ZMod p) S) (N₀ : ℕ) (hN₀ : 0 < N₀)
    (hfin : FiniteDimensional (ZMod p)
      (continuousH2 (r.comp (S ⊓ T N₀).subtype) (Rep.res (Subgroup.inclusion (inf_le_left : S ⊓ T N₀ ≤ S)) B)))
    (hvanish : ∀ z : ↥(S ⊓ T N₀) × ↥(S ⊓ T N₀) → B,
      z ∈ levelCocycles₂ (r.comp (S ⊓ T N₀).subtype) (Rep.res (Subgroup.inclusion (inf_le_left : S ⊓ T N₀ ≤ S)) B) →
      ∃ (N : ℕ) (_ : 0 < N),
        (fun g : ↥((T N).comap (S ⊓ T N₀).subtype) × ↥((T N).comap (S ⊓ T N₀).subtype) =>
            z (((T N).comap (S ⊓ T N₀).subtype).subtype g.1, ((T N).comap (S ⊓ T N₀).subtype).subtype g.2))
          ∈ levelCoboundaries₂ ((r.comp (S ⊓ T N₀).subtype).comp ((T N).comap (S ⊓ T N₀).subtype).subtype)
              (Rep.res ((T N).comap (S ⊓ T N₀).subtype).subtype (Rep.res (Subgroup.inclusion (inf_le_left : S ⊓ T N₀ ≤ S)) B))) :
    ∃ (N : ℕ) (hle : (T N).comap S.subtype ≤ (T N₀).comap S.subtype), 0 < N ∧ N₀ ∣ N ∧
      ∀ b : ↥((T N₀).comap S.subtype) × ↥((T N₀).comap S.subtype) → B,
        b ∈ levelCocycles₂ ((r.comp S.subtype).comp ((T N₀).comap S.subtype).subtype) (Rep.res ((T N₀).comap S.subtype).subtype B) →
        (fun g : ↥((T N).comap S.subtype) × ↥((T N).comap S.subtype) => b (Subgroup.inclusion hle g.1, Subgroup.inclusion hle g.2))
          ∈ levelCoboundaries₂ ((r.comp S.subtype).comp ((T N).comap S.subtype).subtype) (Rep.res ((T N).comap S.subtype).subtype B) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_exists_forall_restrict_comap_mem_levelCoboundaries2_of_finiteDimensional.solution
