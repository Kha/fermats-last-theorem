import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_linearEquiv_tensorProduct_apply_one_tmul_eq_res

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

theorem AlgebraicGeometry.OModulePresheaf.IsQuasicoherent.exists_linearEquiv_tensorProduct_apply_one_tmul_eq_res
    {R : Type u} [CommRing R] {X : Scheme.{u}} {π : X ⟶ Spec (.of R)} (G : OModulePresheaf π)
    (hG : G.IsQuasicoherent) (U V : X.affineOpens) (h : V.1 ≤ U.1) :
    letI := (X.presheaf.map (homOfLE h).op).hom.toAlgebra
    ∃ β : Γ(X, V.1) ⊗[Γ(X, U.1)] G.obj U.1 ≃ₗ[Γ(X, V.1)] G.obj V.1,
      ∀ x : G.obj U.1, β (1 ⊗ₜ x) = G.res h x := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_linearEquiv_tensorProduct_apply_one_tmul_eq_res.solution
