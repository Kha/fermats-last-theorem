import Mathlib
import Definitions.Def_AlgebraicGeometry_FppfSiteCohomology
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_sheaf_smallFppfTopology_specInt_sectionsEquiv_algHom

open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory

theorem HopfAlgebra.exists_sheaf_smallFppfTopology_specInt_sectionsEquiv_algHom
    (H : Type) [CommRing H] [HopfAlgebra ℤ H]

    (hcomm : ∀ (A : Type) [CommRing A] (f g : WithConv (H →ₐ[ℤ] A)), f * g = g * f) :
    ∃ (𝒥 : Sheaf (smallFppfTopology specInt) Ab.{1})
      (e : ∀ U : specInt.Fppf,
        𝒥.1.obj (Opposite.op U) ≃+ Additive (WithConv (H →ₐ[ℤ] Γ(U.left, ⊤)))),
      ∀ {U V : specInt.Fppf} (f : U ⟶ V) (s : 𝒥.1.obj (Opposite.op V)) (h : H),
        (Additive.toMul (e U (𝒥.1.map f.op s))) h
          = (Scheme.Γ.map f.left.op) ((Additive.toMul (e V s)) h) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_sheaf_smallFppfTopology_specInt_sectionsEquiv_algHom.solution
