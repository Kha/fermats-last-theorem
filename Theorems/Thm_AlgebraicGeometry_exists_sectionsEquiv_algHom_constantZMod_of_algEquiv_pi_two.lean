import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Bialgebra.Convolution
import Definitions.Def_AlgebraicGeometry_FppfKummerProp17
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_sectionsEquiv_algHom_constantZMod_of_algEquiv_pi_two
open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory
theorem AlgebraicGeometry.exists_sectionsEquiv_algHom_constantZMod_of_algEquiv_pi_two
    (K : Type) [CommRing K] [HopfAlgebra ℤ K]
    (f : K ≃ₐ[ℤ] (Fin 2 → ℤ)) :
    ∃ e : ∀ T : Scheme.{0},
      ((FppfKummerSES.sheafULift.{0}.obj
          (FppfRepresentableGroupSchemeSheaf.constantZModSheaf.{0} 2)).obj.obj
        (Opposite.op T)) ≃+ Additive (WithConv (K →ₐ[ℤ] Γ(T, ⊤))),
      ∀ {T T' : Scheme.{0}} (g : T ⟶ T')
        (s : (FppfKummerSES.sheafULift.{0}.obj
            (FppfRepresentableGroupSchemeSheaf.constantZModSheaf.{0} 2)).obj.obj
          (Opposite.op T')) (k : K),
        (Additive.toMul (e T ((FppfKummerSES.sheafULift.{0}.obj
            (FppfRepresentableGroupSchemeSheaf.constantZModSheaf.{0} 2)).obj.map g.op s))) k
          = (Scheme.Γ.map g.op) ((Additive.toMul (e T' s)) k) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_sectionsEquiv_algHom_constantZMod_of_algEquiv_pi_two.solution
