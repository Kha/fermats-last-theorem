import Mathlib
import Definitions.Def_AlgebraicGeometry_FppfSiteCohomology
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_sheafHom_sectionsEquiv_algHom_comp_of_bialgHom

open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory

theorem HopfAlgebra.exists_sheafHom_sectionsEquiv_algHom_comp_of_bialgHom
    (F F' : Sheaf (smallFppfTopology specInt) Ab.{1})
    (H H' : Type) [CommRing H] [CommRing H'] [HopfAlgebra ℤ H] [HopfAlgebra ℤ H']
    (eF : ∀ U : specInt.Fppf, F.1.obj (Opposite.op U) ≃+ Additive (WithConv (H →ₐ[ℤ] Γ(U.left, ⊤))))
    (heF : ∀ {U V : specInt.Fppf} (f : U ⟶ V) (s : F.1.obj (Opposite.op V)) (h : H),
        (Additive.toMul (eF U (F.1.map f.op s))) h = (Scheme.Γ.map f.left.op) ((Additive.toMul (eF V s)) h))
    (eF' : ∀ U : specInt.Fppf, F'.1.obj (Opposite.op U) ≃+ Additive (WithConv (H' →ₐ[ℤ] Γ(U.left, ⊤))))
    (heF' : ∀ {U V : specInt.Fppf} (f : U ⟶ V) (s : F'.1.obj (Opposite.op V)) (h : H'),
        (Additive.toMul (eF' U (F'.1.map f.op s))) h = (Scheme.Γ.map f.left.op) ((Additive.toMul (eF' V s)) h))
    (π : H' →ₐc[ℤ] H) :
    ∃ incl : F ⟶ F', ∀ (U : specInt.Fppf) (s : F.1.obj (Opposite.op U)) (h' : H'),
      (Additive.toMul (eF' U (incl.1.app (Opposite.op U) s))) h' = (Additive.toMul (eF U s)) (π h') := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_sheafHom_sectionsEquiv_algHom_comp_of_bialgHom.solution
