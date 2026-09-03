import Mathlib
import Definitions.Def_GroupCohomology_RepPi
import Definitions.Def_GroupCohomology_RelationModule
import Definitions.Def_GroupCohomology_ContinuousUnramified
import P2M.Util
import P2M.Sol.S_groupCohomology_alpha1Read_comp_eq_sum_theta_of_forall_local

set_option autoImplicit false
set_option maxHeartbeats 1600000
p2m_open "CategoryTheory groupCohomology~map_delta_eq_delta_map~exists_corestriction_map_map_res_eq_map_norm ExtCitation"

theorem groupCohomology.alpha1Read_comp_eq_sum_theta_of_forall_local
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes)
    (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (θ : ∀ v : extArithIndex S,
      continuousH1 (extArithLoc S v) (Rep.res (extArithLoc S v) M) →ₗ[ZMod p]
        Module.Dual (ZMod p) (continuousH1 (extArithLoc S v) (Rep.res (extArithLoc S v) (M.dualTwist (cycloChar p)))))
    (hloc : ∀ y ∈ continuousH1S S (M.dualTwist (cycloChar p)), ∀ v : extArithIndex S,
      locTotal (extArithLoc S) (M.dualTwist (cycloChar p)) y v ∈ continuousH1 (extArithLoc S v) (Rep.res (extArithLoc S v) (M.dualTwist (cycloChar p))))

    {G : Type} [Group G] [Fintype G] [DecidableEq G]
    (D : extArithIndex S → Subgroup G) [∀ v, DecidableRel ⇑(QuotientGroup.rightRel (D v))]
    (Yv : ∀ v : extArithIndex S, Rep ℤ ↥(D v)) (C : Rep ℤ G)
    (lam : ∀ v, Yv v ⟶ Rep.res (D v).subtype C)
    (lamJ : GroupCohomology.RepPi.obj (fun v => Rep.coind (D v).subtype (Yv v)) ⟶ C)
    (hlamJ : lamJ = ∑ v, GroupCohomology.RepPi.proj (fun v => Rep.coind (D v).subtype (Yv v)) v ≫
      ((Rep.coindResAdjunction ℤ (D v)).homEquiv (Yv v) C).symm (lam v))

    (B : Rep ℤ G) [Fintype B] (hB : ∀ b : B, p • b = 0)
    (hX : (Rep.relationSeqInt B).ShortExact)
    (hXv : ∀ v, ((Rep.relationSeqInt B).map (Rep.resFunctor (D v).subtype)).ShortExact)

    (invG : ↥(groupCohomology C 2) →+ AddCircle (1 : ℚ))
    (invD : ∀ v, ↥(groupCohomology (Rep.res (D v).subtype C) 2) →+ AddCircle (1 : ℚ))
    (hcor : ∀ (v : extArithIndex S) (cor : ↥(groupCohomology (Rep.res (D v).subtype C) 2) →+ ↥(groupCohomology C 2)),
      (∀ x : ↥(groupCohomology C 2), cor ((groupCohomology.map (D v).subtype (𝟙 (Rep.res (D v).subtype C)) 2).hom x) = (D v).index • x) →
      ∀ y, invG (cor y) = invD v y)

    (al : (Rep.relationModuleInt B ⟶ C) →+ (↥(groupCohomology B 1) →+ ZMod p))
    (hal : ∀ (φ : Rep.relationModuleInt B ⟶ C) (y : ↥(groupCohomology B 1)),
      invG ((groupCohomology.map (MonoidHom.id G) φ 2).hom ((groupCohomology.δ hX 1 2 rfl).hom y)) = ((((al φ y).val : ℚ) / (p : ℚ) : ℚ) : AddCircle (1 : ℚ)))
    (infl : ↥(groupCohomology B 1) →+ H1 (M.dualTwist (cycloChar p)))
    (Λ : ∀ v, (Rep.res (D v).subtype (Rep.relationModuleInt B) ⟶ Yv v) →+ ↥(continuousH1 (extArithLoc S v) (Rep.res (extArithLoc S v) M)))
    (u : extArithIndex S → (ZMod p)ˣ)

    (hLOC : ∀ (v : extArithIndex S) (sv : Rep.res (D v).subtype (Rep.relationModuleInt B) ⟶ Yv v)
        (x : ↥(groupCohomology B 1)) (hx : infl x ∈ continuousH1S S (M.dualTwist (cycloChar p))),
      invD v ((groupCohomology.map (MonoidHom.id ↥(D v)) (sv ≫ lam v) 2).hom
        ((groupCohomology.δ (hXv v) 1 2 rfl).hom
          ((groupCohomology.map (D v).subtype (𝟙 (Rep.res (D v).subtype B)) 1).hom x)))
        = (((((u v : ZMod p) * θ v (Λ v sv) ⟨locTotal (extArithLoc S) (M.dualTwist (cycloChar p)) (infl x) v, hloc _ hx v⟩).val : ℚ) / (p : ℚ) : ℚ) : AddCircle (1 : ℚ)))
    (s : Rep.relationModuleInt B ⟶ GroupCohomology.RepPi.obj (fun v => Rep.coind (D v).subtype (Yv v)))
    (x : ↥(groupCohomology B 1)) (hx : infl x ∈ continuousH1S S (M.dualTwist (cycloChar p))) :
    al (s ≫ lamJ) x = ∑ v, (u v : ZMod p) * θ v
      (Λ v (((Rep.resCoindAdjunction ℤ (D v).subtype).homEquiv (Rep.relationModuleInt B) (Yv v)).symm
        (s ≫ GroupCohomology.RepPi.proj (fun v => Rep.coind (D v).subtype (Yv v)) v)))
      ⟨locTotal (extArithLoc S) (M.dualTwist (cycloChar p)) (infl x) v, hloc _ hx v⟩ := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_alpha1Read_comp_eq_sum_theta_of_forall_local.solution
