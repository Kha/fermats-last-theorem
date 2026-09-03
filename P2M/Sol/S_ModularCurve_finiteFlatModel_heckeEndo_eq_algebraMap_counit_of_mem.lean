import Mathlib
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_GaloisRep_Flat
import Theorems.Thm_HopfAlgebra_eq_of_forall_algHom_algebraicClosure_apply_eq_of_flat_ratLocalizedAt
import P2M.Util
namespace P2MW.S_ModularCurve_finiteFlatModel_heckeEndo_eq_algebraMap_counit_of_mem

set_option autoImplicit false

open ModularCurve WithConv in

theorem solution
    (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime] (𝔪 : Ideal HeckeAlg)
    (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt p) H]
    [Module.Finite (GaloisRep.ratLocalizedAt p) H] [Module.Flat (GaloisRep.ratLocalizedAt p) H]
    (e : letI := heckeModuleBar N
      WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃ ↥(heckeTorsion (JZero N) 𝔪))
    (he_add : letI := heckeModuleBar N
      ∀ f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ), e (f * g) = e f + e g)
    (φ : HeckeAlg → (H →ₐ[GaloisRep.ratLocalizedAt p] H))
    (hφ : letI := heckeModuleBar N
      ∀ (t : HeckeAlg) (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
        (∀ h : H, g h = f (φ t h)) → ((e g : ↥(heckeTorsion (JZero N) 𝔪)) : JZero N) = t • ((e f : ↥(heckeTorsion (JZero N) 𝔪)) : JZero N))
    (t : HeckeAlg) (ht : t ∈ 𝔪) (h : H) :
    φ t h = algebraMap (GaloisRep.ratLocalizedAt p) H (Coalgebra.counit h) := by
  letI := heckeModuleBar N
  apply HopfAlgebra.eq_of_forall_algHom_algebraicClosure_apply_eq_of_flat_ratLocalizedAt p H
  intro f₀
  let f : WithConv (H →ₐ[(GaloisRep.ratLocalizedAt p)] (AlgebraicClosure ℚ)) := toConv f₀
  let g : WithConv (H →ₐ[(GaloisRep.ratLocalizedAt p)] (AlgebraicClosure ℚ)) := toConv (f₀.comp (φ t))
  have hg : ∀ x : H, g x = f (φ t x) := fun x => rfl
  have hm := (e f).2
  rw [mem_heckeTorsion_iff] at hm
  have h0 := (hφ t f g hg).trans (hm t ht)
  have h1 := he_add 1 1
  rw [mul_one] at h1
  have h1' : e 1 = 0 := (add_left_cancel ((add_zero _).trans h1)).symm
  have h2 : e g = 0 := Subtype.ext h0
  have h3 : g = 1 := e.injective (h2.trans h1'.symm)
  have h4 : g h = (1 : WithConv (H →ₐ[(GaloisRep.ratLocalizedAt p)] (AlgebraicClosure ℚ))) h := by
    rw [h3]
  rw [hg, AlgHom.convOne_apply] at h4
  have h5 : f₀ (φ t h) = f₀ (algebraMap (GaloisRep.ratLocalizedAt p) H (Coalgebra.counit h)) := by
    rw [AlgHom.commutes]; exact h4
  exact h5
