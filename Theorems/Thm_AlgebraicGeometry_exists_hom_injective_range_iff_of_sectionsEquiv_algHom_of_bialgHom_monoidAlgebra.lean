import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Bialgebra.Convolution
import Mathlib.RingTheory.Bialgebra.Equiv
import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
import Mathlib.Algebra.MonoidAlgebra.Basic
import Definitions.Def_AlgebraicGeometry_FppfSiteCohomology
import Definitions.Def_AlgebraicGeometry_FppfKummerProp17
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_hom_injective_range_iff_of_sectionsEquiv_algHom_of_bialgHom_monoidAlgebra
open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory

theorem AlgebraicGeometry.exists_hom_injective_range_iff_of_sectionsEquiv_algHom_of_bialgHom_monoidAlgebra
    (p q : ℕ) [NeZero q]
    (K : Type) (_ : CommRing K) (_ : HopfAlgebra ℤ K)
    (ι : MonoidAlgebra ℤ (Multiplicative (ZMod q)) →ₐc[ℤ] K)
    (hι : ∀ (R : Type) [CommRing R],
        (∀ f g : K →ₐ[ℤ] R, f.comp (ι : MonoidAlgebra ℤ (Multiplicative (ZMod q)) →ₐ[ℤ] K) =
            g.comp (ι : MonoidAlgebra ℤ (Multiplicative (ZMod q)) →ₐ[ℤ] K) → f = g) ∧
        ∀ g : MonoidAlgebra ℤ (Multiplicative (ZMod q)) →ₐ[ℤ] R,
          (∃ f : K →ₐ[ℤ] R, f.comp (ι : MonoidAlgebra ℤ (Multiplicative (ZMod q)) →ₐ[ℤ] K) = g) ↔
            ∃ a : R, a - 1 ∈ Ideal.span {(p : R)} ∧
              ∀ h : MonoidAlgebra ℤ (Multiplicative (ZMod q)),
                a * (g h - algebraMap ℤ R
                  (Bialgebra.counitAlgHom ℤ (MonoidAlgebra ℤ (Multiplicative (ZMod q))) h)) = 0)
    (L : Sheaf (smallFppfTopology specInt) Ab.{1})
    (e : ∀ U : specInt.Fppf,
      L.1.obj (Opposite.op U) ≃+ Additive (WithConv (K →ₐ[ℤ] Γ(U.left, ⊤))))
    (hnat : ∀ {U V : specInt.Fppf} (f : U ⟶ V) (s : L.1.obj (Opposite.op V)) (k : K),
      (Additive.toMul (e U (L.1.map f.op s))) k
        = (Scheme.Γ.map f.left.op) ((Additive.toMul (e V s)) k))
    (C : Sheaf (smallFppfTopology specInt) Ab.{1})
    (iC : C.obj ≅ (Scheme.Fppf.forget specInt ⋙ Over.forget specInt).op ⋙
      (FppfKummerSES.muPAbelianSheafLifted.{0} q).obj) :
    ∃ f : L ⟶ C,
      (∀ U : specInt.Fppf, Function.Injective (f.hom.app (Opposite.op U))) ∧
      ∀ (U : specInt.Fppf) (s : C.obj.obj (Opposite.op U)),
        s ∈ Set.range (f.hom.app (Opposite.op U)) ↔
          ∃ a : Γ(U.left, ⊤), a - 1 ∈ Ideal.span {(p : Γ(U.left, ⊤))} ∧
            a * ((FppfKummerSES.gmLiftedSectionUnit
                    ((Limits.kernel.ι (FppfKummerSES.gmPowSelf.{0} q)).hom.app (Opposite.op U.left)
                      (iC.hom.app (Opposite.op U) s)) : Γ(U.left, ⊤)) - 1) = 0 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_hom_injective_range_iff_of_sectionsEquiv_algHom_of_bialgHom_monoidAlgebra.solution
