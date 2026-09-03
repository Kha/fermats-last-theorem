import Definitions.Def_Gamma0HeckeOperatorHom
import P2M.Util
namespace P2MW.S_HeckeEis_coresHom_resHom_apply

open Subgroup

theorem solution {G : Type*} [Group G] (H : Subgroup G) {A : Type*}
    [AddCommGroup A] [H.FiniteIndex] (φ : Additive G →+ A) (g : G) :
    HeckeEis.coresHom H (HeckeEis.resHom H φ) (Additive.ofMul g) =
      H.index • φ (Additive.ofMul g) := by
  letI := H.fintypeQuotientOfFiniteIndex
  have hmul : ∀ x y : G, φ (Additive.ofMul (x * y)) =
      φ (Additive.ofMul x) + φ (Additive.ofMul y) := fun x y => by rw [ofMul_mul, map_add]
  have hinv : ∀ x : G, φ (Additive.ofMul x⁻¹) = -φ (Additive.ofMul x) := fun x => by
    rw [ofMul_inv, map_neg]
  have hreindex := (MulAction.bijective g).sum_comp
    (fun q : G ⧸ H => φ (Additive.ofMul (Quotient.out q)))
  calc HeckeEis.coresHom H (HeckeEis.resHom H φ) (Additive.ofMul g)
      = ∑ q : G ⧸ H, φ (Additive.ofMul ((HeckeEis.transferAux H g q : G))) := rfl
    _ = ∑ q : G ⧸ H, (-φ (Additive.ofMul (g • q).out) +
          (φ (Additive.ofMul g) + φ (Additive.ofMul q.out))) := by
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [HeckeEis.coe_transferAux, hmul, hmul, hinv]
    _ = -(∑ q : G ⧸ H, φ (Additive.ofMul (g • q).out)) +
          ((Fintype.card (G ⧸ H)) • φ (Additive.ofMul g) +
            ∑ q : G ⧸ H, φ (Additive.ofMul q.out)) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_neg_distrib,
          Finset.sum_const, Finset.card_univ]
    _ = H.index • φ (Additive.ofMul g) := by
        rw [hreindex, ← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card]
        abel
