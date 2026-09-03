import Definitions.Def_AlgebraicGeometry_GradedOAlgebraSectionRing
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_rightUnitor_hom_app_tensorSections_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_associator_hom_app_tensorSections_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_tensorHom_app_tensorSections_monoidalV2
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_tensorPowAdd_hom_app_tensorSections_tensorPowSection

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules"

theorem solution
    {X : Scheme.{u}} {L : X.Modules} {U : X.Opens} (g : Γ(L, U)) (m n : ℕ) :
    (Scheme.Modules.tensorPowAdd L m n).hom.app U
        (Scheme.Modules.tensorSections (L := L.tensorPow m) (M := L.tensorPow n)
          (Scheme.Modules.tensorPowSection g m) (Scheme.Modules.tensorPowSection g n)) =
      Scheme.Modules.tensorPowSection g (m + n) := by
  induction n with
  | zero =>
    have h := rightUnitor_hom_app_tensorSections_monoidalV2 (N := L.tensorPow m) (U := U)
      (tensorPowSection g m) (1 : Γ(X, U))
    rw [one_smul] at h
    exact h
  | succ n ih =>
    show ((α_ (L.tensorPow m) (L.tensorPow n) L).symm ≪≫ whiskerRightIso (tensorPowAdd L m n) L).hom.app U
        (tensorSections (L := L.tensorPow m) (M := L.tensorPow n ⊗ L) (tensorPowSection g m)
          (tensorSections (L := L.tensorPow n) (M := L) (tensorPowSection g n) g)) =
      tensorSections (L := L.tensorPow (m + n)) (M := L) (tensorPowSection g (m + n)) g
    have hα : (α_ (L.tensorPow m) (L.tensorPow n) L).inv.app U
        (tensorSections (L := L.tensorPow m) (M := L.tensorPow n ⊗ L) (tensorPowSection g m)
          (tensorSections (L := L.tensorPow n) (M := L) (tensorPowSection g n) g)) =
        tensorSections (L := L.tensorPow m ⊗ L.tensorPow n) (M := L)
          (tensorSections (L := L.tensorPow m) (M := L.tensorPow n) (tensorPowSection g m) (tensorPowSection g n)) g := by
      rw [← associator_hom_app_tensorSections_monoidalV2, ← CategoryTheory.comp_apply, ← Scheme.Modules.Hom.comp_app,
        Iso.hom_inv_id, Scheme.Modules.Hom.id_app, CategoryTheory.id_apply]
    rw [Iso.trans_hom, Iso.symm_hom, whiskerRightIso_hom, Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply, hα,
      ← tensorHom_id, tensorHom_app_tensorSections_monoidalV2, ih, Scheme.Modules.Hom.id_app, CategoryTheory.id_apply]
