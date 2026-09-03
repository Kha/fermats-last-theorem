import Mathlib
import Definitions.Def_GroupCohomology_CyclicCarry
import P2M.Util
import P2M.Sol.S_groupCohomology_exists_natCard_H2_eq_and_span_eq_top_of_carry_of_exists_norm_eq

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits groupCohomology Rep

theorem groupCohomology.exists_natCard_H2_eq_and_span_eq_top_of_carry_of_exists_norm_eq
    {Γ : Type} [Group Γ] [Fintype Γ] (C : Rep ℤ Γ) (S T : Subgroup Γ) [S.Normal] [T.Normal]
    [Fintype (Γ ⧸ S)] (hST : S ⊓ T = ⊥)
    (hS1 : IsZero (groupCohomology (Rep.res S.subtype C) 1))
    (hT1 : IsZero (groupCohomology (Rep.res T.subtype C) 1))
    (s : Γ ⧸ T) (hs : ∀ g : Γ ⧸ T, g ∈ Subgroup.zpowers s) (hsfin : IsOfFinOrder s)
    (t : S) (ht : ∀ g : S, g ∈ Subgroup.zpowers t) (htfin : IsOfFinOrder t)
    (n' : ℕ) (hn' : orderOf s = n') (hn : Fintype.card (Γ ⧸ S) ∣ n')
    (a₀T : C.quotientToInvariants T) (a₀ : C) (ha₀T : (@Representation.quotientToInvariants_lift ℤ Γ _ _ C.V C.hV1 C.hV2 C.ρ T _) a₀T = a₀)
    (ha₀ : ∀ g : Γ, C.ρ g a₀ = a₀)
    (hzT : carryFun s hs hsfin a₀T ∈ cocycles₂ (C.quotientToInvariants T))
    (hord : addOrderOf ((H2π (C.quotientToInvariants T)).hom ⟨carryFun s hs hsfin a₀T, hzT⟩) = n')
    (hnorm : ∃ b : C, (∑ i ∈ Finset.range (orderOf t), C.ρ ((t : Γ) ^ i) b) = (n' / Fintype.card (Γ ⧸ S)) • a₀)
    (hfin : Finite (groupCohomology (C.quotientToInvariants S) 2))
    (hle : Nat.card (groupCohomology (C.quotientToInvariants S) 2) ≤ Fintype.card (Γ ⧸ S)) :
    ∃ y : groupCohomology (C.quotientToInvariants S) 2,
      Nat.card (groupCohomology (C.quotientToInvariants S) 2) = Fintype.card (Γ ⧸ S) ∧
      Submodule.span ℤ {y} = ⊤ ∧
      (map (A := C.quotientToInvariants S) (B := C) (QuotientGroup.mk' S)
          (@Rep.ofHom ℤ Γ _ _ _ _ (C.quotientToInvariants S).hV1 C.hV1 (C.quotientToInvariants S).hV2 C.hV2 _ _ (@Representation.quotientToInvariants_lift ℤ Γ _ _ C.V C.hV1 C.hV2 C.ρ S _)) 2).hom y =
        (n' / Fintype.card (Γ ⧸ S)) •
          (map (A := C.quotientToInvariants T) (B := C) (QuotientGroup.mk' T)
            (@Rep.ofHom ℤ Γ _ _ _ _ (C.quotientToInvariants T).hV1 C.hV1 (C.quotientToInvariants T).hV2 C.hV2 _ _ (@Representation.quotientToInvariants_lift ℤ Γ _ _ C.V C.hV1 C.hV2 C.ρ T _)) 2).hom
              ((H2π (C.quotientToInvariants T)).hom ⟨carryFun s hs hsfin a₀T, hzT⟩) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_exists_natCard_H2_eq_and_span_eq_top_of_carry_of_exists_norm_eq.solution
