import Definitions.Def_AlgebraicGeometry_OModulePresheafLerayDoubleComplex
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_Leray_dV_comp_biAug

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.OModulePresheaf.Leray.dV_comp_biAug
    {R : Type u} [CommRing R] {V' Z : Scheme.{u}} (p : V' ⟶ Z) (πZ : Z ⟶ Spec (.of R))
    (K : Z.OrderedAffineCover) (K' : V'.OrderedAffineCover) (b : ℕ) :
    (OModulePresheaf.Leray.LerayDblCpx p πZ K K').dV 0 b ∘ₗ OModulePresheaf.Leray.biAug p πZ K K' b
      = OModulePresheaf.Leray.biAug p πZ K K' (b + 1) ∘ₗ (OModulePresheaf.unit (p ≫ πZ)).d K' b := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_Leray_dV_comp_biAug.solution
