import Definitions.Def_AlgebraicGeometry_OModulePresheafLerayDoubleComplex
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_Leray_nonempty_HTot_equiv

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.OModulePresheaf.Leray.nonempty_HTot_equiv
    {R : Type u} [CommRing R] {V' Z : Scheme.{u}} (p : V' ⟶ Z) (πZ : Z ⟶ Spec (.of R))
    [IsSeparated πZ] [IsSeparated (p ≫ πZ)] (K : Z.OrderedAffineCover) (K' : V'.OrderedAffineCover) :
    Nonempty (DoubleComplex.HTot (OModulePresheaf.Leray.LerayDblCpx p πZ K K') 0
        ≃ₗ[R] (OModulePresheaf.unit (p ≫ πZ)).H0 K') ∧
      ∀ n : ℕ, Nonempty (DoubleComplex.HTot (OModulePresheaf.Leray.LerayDblCpx p πZ K K') (n + 1)
        ≃ₗ[R] (OModulePresheaf.unit (p ≫ πZ)).HSucc K' n) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_Leray_nonempty_HTot_equiv.solution
