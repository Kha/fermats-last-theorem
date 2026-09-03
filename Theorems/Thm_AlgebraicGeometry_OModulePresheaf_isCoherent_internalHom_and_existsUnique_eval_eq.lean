import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafInternalHom
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_isCoherent_internalHom_and_existsUnique_eval_eq

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

theorem AlgebraicGeometry.OModulePresheaf.isCoherent_internalHom_and_existsUnique_eval_eq
    {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (CommRingCat.of R)) [IsLocallyNoetherian V]
    (F G : OModulePresheaf π)
    (hFc : F.IsCoherent) (hFq : F.IsQuasicoherent) (hGc : G.IsCoherent) (hGq : G.IsQuasicoherent) :
    (internalHom F G).IsCoherent ∧ (internalHom F G).IsQuasicoherent ∧
      ∀ (U : V.affineOpens) (f : F.obj U.1 →ₗ[Γ(V, U.1)] G.obj U.1),
        ∃! φ : (internalHom F G).obj U.1, ∀ x : F.obj U.1, φ.1 ⟨U, le_rfl⟩ x = f x := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_internalHom_and_existsUnique_eval_eq.solution
