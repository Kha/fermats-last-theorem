import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_forall_res_basicOpen_eq

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.exists_forall_res_basicOpen_eq
    {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)} {F : OModulePresheaf π}
    (hF : F.IsQuasicoherent) (U : V.affineOpens) {ι : Type*} [Fintype ι] (h : ι → Γ(V, U.1))
    (hcov : U.1 ≤ ⨆ j, V.basicOpen (h j)) (x : ∀ j, F.obj (V.basicOpen (h j)))
    (hx : ∀ j k, F.res ((V.basicOpen_mul (h j) (h k)).trans_le inf_le_left) (x j) =
      F.res ((V.basicOpen_mul (h j) (h k)).trans_le inf_le_right) (x k)) :
    ∃ y : F.obj U.1, ∀ j, F.res (V.basicOpen_le (h j)) y = x j := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_res_basicOpen_eq.solution
