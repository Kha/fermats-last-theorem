import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_PDivisibleGroup_BaseChange
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_closedImmersion_isIso_torsion_tensorProduct_baseChange_of_isIso_torsion

set_option autoImplicit false

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.exists_closedImmersion_isIso_torsion_tensorProduct_baseChange_of_isIso_torsion
    {R : Type} [CommRing R]
    {J : Scheme.{0}} {f : J ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f) (hc : L.IsCommutative)
    (p h : ℕ) [Fact p.Prime] (G : PDivisibleGroup R p h)
    (ι : ∀ v : ℕ, Spec (CommRingCat.of (G.level v)) ⟶ J)

    (hS1 : ∀ v : ℕ, ι v ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R (G.level v))))

    (hS2 : ∀ v : ℕ, IsClosedImmersion (ι v))

    (hS5 : ∀ (v : ℕ) (B : Type) [CommRing B] [Algebra R B] (x y : G.Point B v)
      (hx : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom x : G.level v →ₐ[R] B) : G.level v →+* B)) ≫ ι v) ≫ f =
        Spec.map (CommRingCat.ofHom (algebraMap R B)))
      (hy : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom y : G.level v →ₐ[R] B) : G.level v →+* B)) ≫ ι v) ≫ f =
        Spec.map (CommRingCat.ofHom (algebraMap R B))),
      Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom (x * y) : G.level v →ₐ[R] B) : G.level v →+* B)) ≫ ι v =
        (L.mul (Spec.map (CommRingCat.ofHom (algebraMap R B))) ⟨_, hx⟩ ⟨_, hy⟩).1)

    (hS6 : ∀ v : ℕ, Spec.map (CommRingCat.ofHom (G.transition v : G.level (v + 1) →+* G.level v)) ≫ ι (v + 1) = ι v)

    (hS8 : ∀ (v : ℕ), ∃ h3 : ι v ≫ L.schemeNsmul (p ^ v) = (ι v ≫ f) ≫ (L.one (𝟙 (Spec (CommRingCat.of R)))).1,
      IsIso (pullback.lift (f := L.schemeNsmul (p ^ v)) (g := (L.one (𝟙 (Spec (CommRingCat.of R)))).1) (ι v) (ι v ≫ f) h3))

    (R' : Type) [CommRing R'] [Nontrivial R'] [Algebra R R'] :
    let σ : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R) := Spec.map (CommRingCat.ofHom (algebraMap R R'))

    ∃ ι' : ∀ v : ℕ, Spec (CommRingCat.of ((G.baseChange R').level v)) ⟶ pullback f σ,

      (∀ v : ℕ, ι' v ≫ pullback.snd f σ = Spec.map (CommRingCat.ofHom (algebraMap R' ((G.baseChange R').level v)))) ∧
      (∀ v : ℕ, ι' v ≫ pullback.fst f σ =
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom : G.level v →+* (G.baseChange R').level v)) ≫ ι v) ∧

      (∀ v : ℕ, IsClosedImmersion (ι' v)) ∧

      (∀ (v : ℕ) (B : Type) [CommRing B] [Algebra R' B] (x y : (G.baseChange R').Point B v)
        (hx : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom x : (G.baseChange R').level v →ₐ[R'] B) : (G.baseChange R').level v →+* B)) ≫ ι' v) ≫ pullback.snd f σ =
          Spec.map (CommRingCat.ofHom (algebraMap R' B)))
        (hy : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom y : (G.baseChange R').level v →ₐ[R'] B) : (G.baseChange R').level v →+* B)) ≫ ι' v) ≫ pullback.snd f σ =
          Spec.map (CommRingCat.ofHom (algebraMap R' B))),
        Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom (x * y) : (G.baseChange R').level v →ₐ[R'] B) : (G.baseChange R').level v →+* B)) ≫ ι' v =
          ((L.baseChange σ).mul (Spec.map (CommRingCat.ofHom (algebraMap R' B))) ⟨_, hx⟩ ⟨_, hy⟩).1) ∧

      (∀ v : ℕ, Spec.map (CommRingCat.ofHom
          ((G.baseChange R').transition v : (G.baseChange R').level (v + 1) →+* (G.baseChange R').level v)) ≫ ι' (v + 1) = ι' v) ∧

      (∀ (v : ℕ), ∃ h3 : ι' v ≫ (L.baseChange σ).schemeNsmul (p ^ v) =
            (ι' v ≫ pullback.snd f σ) ≫ ((L.baseChange σ).one (𝟙 (Spec (CommRingCat.of R')))).1,
        IsIso (pullback.lift (f := (L.baseChange σ).schemeNsmul (p ^ v)) (g := ((L.baseChange σ).one (𝟙 (Spec (CommRingCat.of R')))).1)
          (ι' v) (ι' v ≫ pullback.snd f σ) h3)) ∧

      (∀ (E : NeronModelInfra.SchemeHomOver (pullback.snd f σ) (pullback.snd f σ)),
        (∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of R')) (x y : NeronModelInfra.SchemeHomOver s (pullback.snd f σ)),
          NeronModelInfra.schemeHomOverComp ((L.baseChange σ).mul s x y) E =
            (L.baseChange σ).mul s (NeronModelInfra.schemeHomOverComp x E) (NeronModelInfra.schemeHomOverComp y E)) →
        ∃ ψ : ∀ v : ℕ, (G.baseChange R').level v →ₐc[R'] (G.baseChange R').level v,
          (∀ v : ℕ, ((G.baseChange R').transition v).comp (ψ (v + 1)) = (ψ v).comp ((G.baseChange R').transition v)) ∧
          ∀ v : ℕ, Spec.map (CommRingCat.ofHom (ψ v : (G.baseChange R').level v →+* (G.baseChange R').level v)) ≫ ι' v = ι' v ≫ E.1) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_closedImmersion_isIso_torsion_tensorProduct_baseChange_of_isIso_torsion.solution
