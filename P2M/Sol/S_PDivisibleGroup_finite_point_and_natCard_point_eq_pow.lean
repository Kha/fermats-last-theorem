import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_PDivisibleGroup_Points
import Theorems.Thm_HopfAlgebra_algebra_etale_of_module_finite_of_charZero
import Theorems.Thm_AlgHom_natCard_eq_finrank_of_isReduced_of_isAlgClosed
import P2M.Util
namespace P2MW.S_PDivisibleGroup_finite_point_and_natCard_point_eq_pow

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
set_option Elab.async false

open scoped TensorProduct

theorem solution
    (p : ℕ) [Fact p.Prime]
    {O : Type} [CommRing O] {h : ℕ} (H : PDivisibleGroup O p h)
    (L : Type) [Field L] [IsAlgClosed L] [CharZero L] [Algebra O L] (v : ℕ) :
    Finite (H.Point L v) ∧ Nat.card (H.Point L v) = p ^ (v * h) := by
  classical
  haveI : Nontrivial O := (algebraMap O L).domain_nontrivial
  haveI : Algebra.Etale L (L ⊗[O] H.level v) := HopfAlgebra.algebra_etale_of_module_finite_of_charZero L _
  haveI : IsReduced (L ⊗[O] H.level v) := Algebra.FormallyUnramified.isReduced_of_field L _
  have hcardB : Nat.card (L ⊗[O] H.level v →ₐ[L] L) = p ^ (v * h) := by
    rw [AlgHom.natCard_eq_finrank_of_isReduced_of_isAlgClosed, Module.finrank_baseChange, H.finrank_level]

  let e : H.Point L v ≃ (L ⊗[O] H.level v →ₐ[L] L) :=
    { toFun := fun x => Algebra.TensorProduct.lift (AlgHom.id L L) (PDivisibleGroup.Point.toAlgHom x)
        (fun _ _ => Commute.all _ _)
      invFun := fun φ => PDivisibleGroup.Point.ofAlgHom
        ((φ.restrictScalars O).comp (Algebra.TensorProduct.includeRight : H.level v →ₐ[O] L ⊗[O] H.level v))
      left_inv := fun x => PDivisibleGroup.Point.ext fun a => by
        rw [PDivisibleGroup.Point.toAlgHom_ofAlgHom, AlgHom.comp_apply, AlgHom.restrictScalars_apply,
          Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
      right_inv := fun φ => by
        refine Algebra.TensorProduct.ext (Subsingleton.elim _ _) (AlgHom.ext fun a => ?_)
        rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.restrictScalars_apply, AlgHom.restrictScalars_apply,
          Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.lift_tmul, map_one, one_mul,
          PDivisibleGroup.Point.toAlgHom_ofAlgHom, AlgHom.comp_apply, AlgHom.restrictScalars_apply,
          Algebra.TensorProduct.includeRight_apply] }
  have hcard : Nat.card (H.Point L v) = p ^ (v * h) := by rw [Nat.card_congr e, hcardB]
  exact ⟨Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero), hcard⟩
