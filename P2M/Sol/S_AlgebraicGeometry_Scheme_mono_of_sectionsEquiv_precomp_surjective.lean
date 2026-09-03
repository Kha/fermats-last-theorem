import Mathlib
import Definitions.Def_AlgebraicGeometry_FppfSiteCohomology
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Scheme_mono_of_sectionsEquiv_precomp_surjective

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v

theorem solution
    (F F' : Sheaf (smallFppfTopology specInt) Ab.{1})
    (H H' : Type) [CommRing H] [CommRing H'] [HopfAlgebra ℤ H] [HopfAlgebra ℤ H']
    (eF : ∀ U : specInt.Fppf, F.1.obj (op U) ≃+ Additive (WithConv (H →ₐ[ℤ] Γ(U.left, ⊤))))
    (eF' : ∀ U : specInt.Fppf, F'.1.obj (op U) ≃+ Additive (WithConv (H' →ₐ[ℤ] Γ(U.left, ⊤))))
    (π : H' →ₐ[ℤ] H) (hπ : Function.Surjective π)
    (incl : F ⟶ F')
    (hincl : ∀ (U : specInt.Fppf) (s : F.1.obj (op U)) (h' : H'),
      (Additive.toMul (eF' U (incl.1.app (op U) s))) h' = (Additive.toMul (eF U s)) (π h')) :
    Mono incl := by
  haveI : Mono incl.1 := by
    rw [NatTrans.mono_iff_mono_app]
    intro U
    rw [AddCommGrpCat.mono_iff_injective]
    intro s t hst
    apply (eF U.unop).injective
    apply Additive.toMul.injective
    apply WithConv.ext
    apply AlgHom.ext
    intro h
    obtain ⟨h', rfl⟩ := hπ h
    rw [← hincl U.unop s h', ← hincl U.unop t h']
    exact congrArg (fun x => (Additive.toMul ((eF' U.unop) x)).ofConv h') hst
  exact Sheaf.Hom.mono_of_presheaf_mono _ _ incl
