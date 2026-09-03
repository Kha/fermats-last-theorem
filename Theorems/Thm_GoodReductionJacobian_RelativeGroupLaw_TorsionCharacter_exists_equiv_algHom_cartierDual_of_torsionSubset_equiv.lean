import Mathlib
import Definitions.Def_AlgebraicGeometry_TorsionCharacter
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualInstances
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_TorsionCharacter_exists_equiv_algHom_cartierDual_of_torsionSubset_equiv

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.TorsionCharacter.exists_equiv_algHom_cartierDual_of_torsionSubset_equiv
    {S : Type u} [CommRing S] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (n : ℕ)
    {R : Type u} [CommRing R] (ι : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S))
    (H : Type u) [CommRing H] [HopfAlgebra R H] [Module.Finite R H] [Module.Free R H] [Coalgebra.IsCocomm R H]
    (e : ∀ (T : Type u) [CommRing T] [Algebra R T],
      WithConv (H →ₐ[R] T) ≃ L.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap R T)) ≫ ι) n)
    (he_mul : ∀ (T : Type u) [CommRing T] [Algebra R T] (φ ψ : WithConv (H →ₐ[R] T)),
      ((e T (φ * ψ)).val : SchemeHomOver _ f) = L.mul _ (e T φ).val (e T ψ).val)
    (he_nat : ∀ (T T' : Type u) [CommRing T] [Algebra R T] [CommRing T'] [Algebra R T']
        (g : T →ₐ[R] T') (φ : WithConv (H →ₐ[R] T)),
      ((e T' (.toConv (g.comp φ.ofConv))).val : SchemeHomOver _ f).1 =
        Spec.map (CommRingCat.ofHom g.toRingHom) ≫ (e T φ).val.1) :
    ∃ Ψ : ∀ (R' : Type u) [CommRing R'] [Algebra R R'],
        L.TorsionCharacter n (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ ι) ≃ (CartierDual R H →ₐ[R] R'),

      (∀ (R' R'' : Type u) [CommRing R'] [Algebra R R'] [CommRing R''] [Algebra R R''] (g : R' →ₐ[R] R'')
          (χ' : L.TorsionCharacter n (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ ι))
          (χ'' : L.TorsionCharacter n (Spec.map (CommRingCat.ofHom (algebraMap R R'')) ≫ ι)),
          (∀ (T : Type u) [CommRing T] (κ'' : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of R''))
              (x'' : SchemeHomOver (κ'' ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R'')) ≫ ι)) f)
              (hx'' : L.IsTorsionPoint _ n x'')
              (x' : SchemeHomOver ((κ'' ≫ Spec.map (CommRingCat.ofHom g.toRingHom)) ≫
                (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ ι)) f)
              (hx' : L.IsTorsionPoint _ n x'),
              x''.1 = x'.1 →
                χ''.val T κ'' x'' hx'' = χ'.val T (κ'' ≫ Spec.map (CommRingCat.ofHom g.toRingHom)) x' hx') →
          Ψ R'' χ'' = g.comp (Ψ R' χ')) ∧

      (∀ (R' : Type u) [CommRing R'] [Algebra R R']
          (χ₁ χ₂ χ₃ : L.TorsionCharacter n (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ ι)),
          (∀ (T : Type u) [CommRing T] (κ : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of R'))
              (x : SchemeHomOver (κ ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ ι)) f)
              (hx : L.IsTorsionPoint _ n x),
              χ₃.val T κ x hx = χ₁.val T κ x hx * χ₂.val T κ x hx) →
          Ψ R' χ₃ = (WithConv.toConv (Ψ R' χ₁) * WithConv.toConv (Ψ R' χ₂)).ofConv) ∧
      (∀ (R' : Type u) [CommRing R'] [Algebra R R']
          (χ : L.TorsionCharacter n (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ ι)),
          (∀ (T : Type u) [CommRing T] (κ : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of R'))
              (x : SchemeHomOver (κ ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ ι)) f)
              (hx : L.IsTorsionPoint _ n x), χ.val T κ x hx = 1) →
          Ψ R' χ = (1 : WithConv (CartierDual R H →ₐ[R] R')).ofConv) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_TorsionCharacter_exists_equiv_algHom_cartierDual_of_torsionSubset_equiv.solution
