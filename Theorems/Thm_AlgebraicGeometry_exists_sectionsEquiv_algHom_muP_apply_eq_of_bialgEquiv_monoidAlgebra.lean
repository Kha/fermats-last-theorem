import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Bialgebra.Convolution
import Mathlib.RingTheory.Bialgebra.Equiv
import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
import Mathlib.Algebra.MonoidAlgebra.Basic
import Definitions.Def_AlgebraicGeometry_FppfKummerProp17
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_sectionsEquiv_algHom_muP_apply_eq_of_bialgEquiv_monoidAlgebra
open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory

theorem AlgebraicGeometry.exists_sectionsEquiv_algHom_muP_apply_eq_of_bialgEquiv_monoidAlgebra
    (n : ℕ) [NeZero n]
    (K : Type) [CommRing K] [HopfAlgebra ℤ K]
    (f : K ≃ₐc[ℤ] MonoidAlgebra ℤ (Multiplicative (ZMod n))) :
    ∃ e : ∀ T : Scheme.{0},
      ((FppfKummerSES.muPAbelianSheafLifted.{0} n).obj.obj (Opposite.op T)) ≃+
        Additive (WithConv (K →ₐ[ℤ] Γ(T, ⊤))),
      (∀ {T T' : Scheme.{0}} (g : T ⟶ T')
        (s : (FppfKummerSES.muPAbelianSheafLifted.{0} n).obj.obj (Opposite.op T')) (k : K),
        (Additive.toMul (e T ((FppfKummerSES.muPAbelianSheafLifted.{0} n).obj.map g.op s))) k
          = (Scheme.Γ.map g.op) ((Additive.toMul (e T' s)) k)) ∧
      ∀ (T : Scheme.{0}) (s : (FppfKummerSES.muPAbelianSheafLifted.{0} n).obj.obj (Opposite.op T)),
        (Additive.toMul (e T s)) (f.symm (MonoidAlgebra.single (Multiplicative.ofAdd 1) 1))
          = (FppfKummerSES.gmLiftedSectionUnit
              ((Limits.kernel.ι (FppfKummerSES.gmPowSelf.{0} n)).hom.app (Opposite.op T) s) : Γ(T, ⊤)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_sectionsEquiv_algHom_muP_apply_eq_of_bialgEquiv_monoidAlgebra.solution
