import Mathlib
import P2M.Util
import P2M.Sol.S_groupCohomology_exists_natCard_H2_eq_and_span_eq_top_of_map_res_inf_smul_eq_zero

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits groupCohomology Rep

theorem groupCohomology.exists_natCard_H2_eq_and_span_eq_top_of_map_res_inf_smul_eq_zero
    {k Γ : Type} [CommRing k] [Group Γ] [Fintype Γ] (C : Rep k Γ) (S T : Subgroup Γ) [S.Normal] [T.Normal]
    [Fintype (Γ ⧸ S)]
    (hS1 : IsZero (groupCohomology (Rep.res S.subtype C) 1))
    (hT1 : IsZero (groupCohomology (Rep.res T.subtype C) 1))
    (n' : ℕ) (hn : Fintype.card (Γ ⧸ S) ∣ n') (hn'0 : n' ≠ 0)
    (u' : groupCohomology (C.quotientToInvariants T) 2) (hu' : addOrderOf u' = n')
    (hres : (map S.subtype (𝟙 (Rep.res S.subtype C)) 2).hom
        ((n' / Fintype.card (Γ ⧸ S)) •
          (map (A := C.quotientToInvariants T) (B := C) (QuotientGroup.mk' T)
            (ofHom (C.ρ.quotientToInvariants_lift T)) 2).hom u') = 0)
    (hfin : Finite (groupCohomology (C.quotientToInvariants S) 2))
    (hle : Nat.card (groupCohomology (C.quotientToInvariants S) 2) ≤ Fintype.card (Γ ⧸ S)) :
    ∃ y : groupCohomology (C.quotientToInvariants S) 2,
      Nat.card (groupCohomology (C.quotientToInvariants S) 2) = Fintype.card (Γ ⧸ S) ∧
      Submodule.span k {y} = ⊤ ∧
      (map (A := C.quotientToInvariants S) (B := C) (QuotientGroup.mk' S)
          (ofHom (C.ρ.quotientToInvariants_lift S)) 2).hom y =
        (n' / Fintype.card (Γ ⧸ S)) •
          (map (A := C.quotientToInvariants T) (B := C) (QuotientGroup.mk' T)
            (ofHom (C.ρ.quotientToInvariants_lift T)) 2).hom u' := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_exists_natCard_H2_eq_and_span_eq_top_of_map_res_inf_smul_eq_zero.solution
