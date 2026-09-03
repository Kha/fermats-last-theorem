import Definitions.Def_AlgebraicGeometry_OModulePresheafLerayDoubleComplex
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_Leray_nonempty_relHPresheaf_obj_equiv_of_isAffineOpen

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.OModulePresheaf.Leray.nonempty_relHPresheaf_obj_equiv_of_isAffineOpen
    {R : Type u} [CommRing R] {V' Z : Scheme.{u}} (p : V' ⟶ Z) (πZ : Z ⟶ Spec (.of R)) [IsSeparated πZ]
    (K' : V'.OrderedAffineCover) {U : Z.Opens} (hU : IsAffineOpen U) :
    Nonempty ((OModulePresheaf.Leray.relHPresheaf p πZ K' 0).obj U
        ≃ₗ[R] (OModulePresheaf.Leray.restrictToPreimage p πZ K' hU).H0 (p ≫ πZ)) ∧
      ∀ b : ℕ, Nonempty ((OModulePresheaf.Leray.relHPresheaf p πZ K' (b + 1)).obj U
        ≃ₗ[R] (OModulePresheaf.Leray.restrictToPreimage p πZ K' hU).HSucc (p ≫ πZ) b) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_Leray_nonempty_relHPresheaf_obj_equiv_of_isAffineOpen.solution
