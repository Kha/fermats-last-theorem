import Mathlib
import Definitions.Def_AlgebraicGeometry_FppfSiteCohomology
import P2M.Util
namespace P2MW.S_HopfAlgebra_exists_sheafHom_sectionsEquiv_algHom_comp_of_bialgHom

set_option autoImplicit false

open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory Opposite

theorem solution
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
      (Additive.toMul (eF' U (incl.1.app (Opposite.op U) s))) h' = (Additive.toMul (eF U s)) (π h') := by
  classical

  let pre : ∀ U : specInt.Fppf, Additive (WithConv (H →ₐ[ℤ] Γ(U.left, ⊤))) → Additive (WithConv (H' →ₐ[ℤ] Γ(U.left, ⊤))) :=
    fun U x => Additive.ofMul (WithConv.toConv ((Additive.toMul x).ofConv.comp (π : H' →ₐ[ℤ] H)))
  have pre_add : ∀ (U : specInt.Fppf) (x y : Additive (WithConv (H →ₐ[ℤ] Γ(U.left, ⊤)))),
      pre U (x + y) = pre U x + pre U y := by
    intro U x y
    change Additive.ofMul (WithConv.toConv ((Additive.toMul x * Additive.toMul y).ofConv.comp (π : H' →ₐ[ℤ] H))) =
      Additive.ofMul (WithConv.toConv ((Additive.toMul x).ofConv.comp (π : H' →ₐ[ℤ] H)) *
        WithConv.toConv ((Additive.toMul y).ofConv.comp (π : H' →ₐ[ℤ] H)))
    rw [AlgHom.convMul_comp_bialgHom_distrib]
  let φ : ∀ U : specInt.Fppf, F.1.obj (op U) →+ F'.1.obj (op U) := fun U =>
    AddMonoidHom.mk' (fun s => (eF' U).symm (pre U (eF U s))) (fun s t => by
      show (eF' U).symm (pre U (eF U (s + t))) = (eF' U).symm (pre U (eF U s)) + (eF' U).symm (pre U (eF U t))
      rw [map_add, pre_add, map_add])
  have hφ : ∀ (U : specInt.Fppf) (s : F.1.obj (op U)) (h' : H'),
      (Additive.toMul (eF' U (φ U s))) h' = (Additive.toMul (eF U s)) (π h') := by
    intro U s h'
    change (Additive.toMul (eF' U ((eF' U).symm (pre U (eF U s))))) h' = _
    rw [AddEquiv.apply_symm_apply]
    rfl

  have hnat : ∀ {U V : specInt.Fppf} (f : U ⟶ V) (s : F.1.obj (op V)),
      φ U (F.1.map f.op s) = F'.1.map f.op (φ V s) := by
    intro U V f s
    apply (eF' U).injective
    apply Additive.toMul.injective
    apply WithConv.ext
    apply AlgHom.ext
    intro h'
    change (Additive.toMul (eF' U (φ U (F.1.map f.op s)))) h' = (Additive.toMul (eF' U (F'.1.map f.op (φ V s)))) h'
    rw [hφ, heF, heF', hφ]
  refine ⟨⟨{ app := fun U => AddCommGrpCat.ofHom (φ U.unop)
             naturality := ?_ }⟩, fun U s h' => hφ U s h'⟩
  intro X Y g
  ext s
  change φ Y.unop (F.1.map g s) = F'.1.map g (φ X.unop s)
  exact hnat g.unop s
