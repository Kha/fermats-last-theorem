import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_bijective_pi_map_of_fppf_sheaf

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

theorem AlgebraicGeometry.Scheme.bijective_pi_map_of_fppf_sheaf
    (E : Sheaf Scheme.fppfTopology.{u} AddCommGrpCat.{u + 1}) {ι : Type u} [Finite ι] (A : ι → CommRingCat.{u}) :
    Function.Bijective (fun (x : ToType (E.obj.obj (op (Spec (CommRingCat.of (∀ i, A i)))))) (i : ι) =>
      E.obj.map (Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun i => A i) i))).op x) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_bijective_pi_map_of_fppf_sheaf.solution
