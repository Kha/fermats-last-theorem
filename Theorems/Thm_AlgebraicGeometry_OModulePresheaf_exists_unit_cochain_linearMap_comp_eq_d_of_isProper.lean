import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper
attribute [-simp] AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

theorem AlgebraicGeometry.OModulePresheaf.exists_unit_cochain_linearMap_comp_eq_d_of_isProper
    {A : Type u} [CommRing A] [IsNoetherianRing A] {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    (F : OModulePresheaf q) (hc : F.IsCoherent) (hqc : F.IsQuasicoherent) (K : P.OrderedAffineCover) :
    ∃ (Y : Scheme.{u}) (q' : Y ⟶ Spec (CommRingCat.of A)) (_ : IsProper q') (K' : Y.OrderedAffineCover)
      (L : ∀ j : ℕ, F.cochain K j →ₗ[A] (OModulePresheaf.unit q').cochain K' j)
      (Q : ∀ j : ℕ, (OModulePresheaf.unit q').cochain K' j →ₗ[A] F.cochain K j),
      (∀ (j : ℕ) (x : F.cochain K j), Q j (L j x) = x) ∧
      (∀ (j : ℕ) (x : F.cochain K j), (OModulePresheaf.unit q').d K' j (L j x) = L (j + 1) (F.d K j x)) ∧
      (∀ (j : ℕ) (y : (OModulePresheaf.unit q').cochain K' j),
        F.d K j (Q j y) = Q (j + 1) ((OModulePresheaf.unit q').d K' j y)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper.solution
