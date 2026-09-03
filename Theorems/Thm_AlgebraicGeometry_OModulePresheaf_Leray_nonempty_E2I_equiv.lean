import Definitions.Def_AlgebraicGeometry_OModulePresheafLerayDoubleComplex
import Mathlib.LinearAlgebra.Quotient.Pi
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_Leray_nonempty_E2I_equiv

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.OModulePresheaf.Leray.nonempty_E2I_equiv
    {R : Type u} [CommRing R] {V' Z : Scheme.{u}} (p : V' ⟶ Z) (πZ : Z ⟶ Spec (.of R))
    (K : Z.OrderedAffineCover) (K' : V'.OrderedAffineCover) :
    (∀ b : ℕ, Nonempty (DoubleComplex.E₂I (OModulePresheaf.Leray.LerayDblCpx p πZ K K') 0 b
        ≃ₗ[R] (OModulePresheaf.Leray.relHPresheaf p πZ K' b).H0 K)) ∧
      ∀ a b : ℕ, Nonempty (DoubleComplex.E₂I (OModulePresheaf.Leray.LerayDblCpx p πZ K K') (a + 1) b
        ≃ₗ[R] (OModulePresheaf.Leray.relHPresheaf p πZ K' b).HSucc K a) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_Leray_nonempty_E2I_equiv.solution
