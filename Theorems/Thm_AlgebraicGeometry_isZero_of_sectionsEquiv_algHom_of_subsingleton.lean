import Definitions.Def_AlgebraicGeometry_FppfSiteCohomology
import Definitions.Def_GaloisRep_Flat
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isZero_of_sectionsEquiv_algHom_of_subsingleton
open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory

theorem AlgebraicGeometry.isZero_of_sectionsEquiv_algHom_of_subsingleton
    (p : ℕ) [Fact p.Prime]
    (K : Type) (_ : CommRing K) (_ : HopfAlgebra ℤ K) (_ : Algebra.FiniteType ℤ K)
    (_ : Module.Flat ℤ K)
    (hff : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p →
      Module.Finite (GaloisRep.ratLocalizedAt ℓ) (TensorProduct ℤ (GaloisRep.ratLocalizedAt ℓ) K))
    (hgen : Subsingleton (K →ₐ[ℤ] AlgebraicClosure ℚ))
    (L : Sheaf (smallFppfTopology specInt) Ab.{1})
    (e : ∀ U : specInt.Fppf,
      L.1.obj (Opposite.op U) ≃+ Additive (WithConv (K →ₐ[ℤ] Γ(U.left, ⊤)))) :
    Limits.IsZero L := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isZero_of_sectionsEquiv_algHom_of_subsingleton.solution
