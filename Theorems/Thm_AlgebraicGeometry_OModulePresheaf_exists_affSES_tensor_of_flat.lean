import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafTensor
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_affSES_tensor_of_flat

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry TensorProduct

theorem AlgebraicGeometry.OModulePresheaf.exists_affSES_tensor_of_flat
    {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)}
    {F₁ F₂ F₃ : OModulePresheaf π} (S : OModulePresheaf.AffSES F₁ F₂ F₃) (G : OModulePresheaf π)
    (hG : ∀ U : V.affineOpens, Module.Flat Γ(V, U.1) (G.obj U.1)) :
    ∃ S' : OModulePresheaf.AffSES (F₁.tensor G) (F₂.tensor G) (F₃.tensor G),
      ∀ U : V.affineOpens,
        (∀ (x : F₁.obj U.1) (y : G.obj U.1),
          S'.inc.app U (show (F₁.tensor G).obj U.1 from x ⊗ₜ[Γ(V, U.1)] y) =
            (show (F₂.tensor G).obj U.1 from S.inc.app U x ⊗ₜ[Γ(V, U.1)] y)) ∧
        (∀ (x : F₂.obj U.1) (y : G.obj U.1),
          S'.proj.app U (show (F₂.tensor G).obj U.1 from x ⊗ₜ[Γ(V, U.1)] y) =
            (show (F₃.tensor G).obj U.1 from S.proj.app U x ⊗ₜ[Γ(V, U.1)] y)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affSES_tensor_of_flat.solution
