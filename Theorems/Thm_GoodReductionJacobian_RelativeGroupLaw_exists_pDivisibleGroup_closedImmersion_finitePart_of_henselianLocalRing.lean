import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_pDivisibleGroup_closedImmersion_finitePart_of_henselianLocalRing
attribute [-simp] GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.exists_pDivisibleGroup_closedImmersion_finitePart_of_henselianLocalRing
    {R : Type} [CommRing R] [HenselianLocalRing R]
    {X : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of R)} [IsSeparated f] [LocallyOfFiniteType f]
    (L : RelativeGroupLaw R f) (hc : L.IsCommutative) (p h : ℕ)
    (hlqf : ∀ v : ℕ, LocallyQuasiFinite (L.schemeKerStr (p ^ v)))
    (hqc : ∀ v : ℕ, QuasiCompact (L.schemeKerStr (p ^ v)))
    (hflat : ∀ v : ℕ, Flat (L.schemeKerStr (p ^ v)))

    (hrank : ∀ (v : ℕ) (H : Type) [CommRing H] [Algebra R H] [Module.Finite R H] [Module.Free R H]
      (j : Spec (CommRingCat.of H) ⟶ L.schemeKer (p ^ v)),
      j ≫ L.schemeKerStr (p ^ v) = Spec.map (CommRingCat.ofHom (algebraMap R H)) →
      IsOpenImmersion j → IsClosedImmersion j →
      (∀ x : ↥(L.schemeKer (p ^ v)), (L.schemeKerStr (p ^ v)).base x = IsLocalRing.closedPoint R →
        x ∈ Set.range j.base) →
      Module.finrank R H = p ^ (v * h)) :
    ∃ (G : PDivisibleGroup R p h) (ι : ∀ v : ℕ, Spec (CommRingCat.of (G.level v)) ⟶ X),

      (∀ v : ℕ, ι v ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R (G.level v)))) ∧

      (∀ v : ℕ, IsClosedImmersion (ι v)) ∧

      (∀ v : ℕ, ι v ≫ L.schemeNsmul (p ^ v) = (ι v ≫ f) ≫ (L.one (𝟙 (Spec (CommRingCat.of R)))).1) ∧

      (∀ (v : ℕ) (B : Type) [CommRing B] [Algebra R B] (x y : G.Point B v)
        (hx : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom x : G.level v →ₐ[R] B) : G.level v →+* B)) ≫ ι v) ≫ f =
          Spec.map (CommRingCat.ofHom (algebraMap R B)))
        (hy : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom y : G.level v →ₐ[R] B) : G.level v →+* B)) ≫ ι v) ≫ f =
          Spec.map (CommRingCat.ofHom (algebraMap R B))),
        Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom (x * y) : G.level v →ₐ[R] B) : G.level v →+* B)) ≫ ι v =
          (L.mul (Spec.map (CommRingCat.ofHom (algebraMap R B))) ⟨_, hx⟩ ⟨_, hy⟩).1) ∧

      (∀ v : ℕ, Spec.map (CommRingCat.ofHom (G.transition v : G.level (v + 1) →+* G.level v)) ≫ ι (v + 1) = ι v) ∧

      (∀ (E : SchemeHomOver f f),
        (∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver s f),
          NeronModelInfra.schemeHomOverComp (L.mul s x y) E =
            L.mul s (NeronModelInfra.schemeHomOverComp x E) (NeronModelInfra.schemeHomOverComp y E)) →
        ∃ φ : ∀ v : ℕ, G.level v →ₐc[R] G.level v,
          (∀ v : ℕ, (G.transition v).comp (φ (v + 1)) = (φ v).comp (G.transition v)) ∧
          ∀ v : ℕ, Spec.map (CommRingCat.ofHom (φ v : G.level v →+* G.level v)) ≫ ι v = ι v ≫ E.1) ∧

      (∀ (v : ℕ)
        (h3 : ι v ≫ L.schemeNsmul (p ^ v) = (ι v ≫ f) ≫ (L.one (𝟙 (Spec (CommRingCat.of R)))).1),
        IsOpenImmersion (pullback.lift (f := L.schemeNsmul (p ^ v)) (g := (L.one (𝟙 (Spec (CommRingCat.of R)))).1)
            (ι v) (ι v ≫ f) h3) ∧
        IsClosedImmersion (pullback.lift (f := L.schemeNsmul (p ^ v)) (g := (L.one (𝟙 (Spec (CommRingCat.of R)))).1)
            (ι v) (ι v ≫ f) h3) ∧
        ∀ x : ↥(L.schemeKer (p ^ v)), (L.schemeKerStr (p ^ v)).base x = IsLocalRing.closedPoint R →
          x ∈ Set.range (pullback.lift (f := L.schemeNsmul (p ^ v)) (g := (L.one (𝟙 (Spec (CommRingCat.of R)))).1)
            (ι v) (ι v ≫ f) h3).base) ∧

      (∀ (v : ℕ) (T : Type) [CommRing T] [Algebra R T] [Module.Finite R T]
        (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R T))) f),
        L.IsTorsionPoint _ (p ^ v) x →
        ∃ φ : G.level v →ₐ[R] T, Spec.map (CommRingCat.ofHom (φ : G.level v →+* T)) ≫ ι v = x.1) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_pDivisibleGroup_closedImmersion_finitePart_of_henselianLocalRing.solution
