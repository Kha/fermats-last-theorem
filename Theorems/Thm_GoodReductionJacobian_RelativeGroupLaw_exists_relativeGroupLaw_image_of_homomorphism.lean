import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism
attribute [-simp] GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.exists_relativeGroupLaw_image_of_homomorphism
    {k : Type u} [Field k]
    {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of k)} (L : RelativeGroupLaw k f)
    (hJ : AbelianSchemePropertyBundle k f)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t f),
      L.mul t x y = L.mul t y x)
    {X : Scheme.{u}} {g : X ⟶ Spec (CommRingCat.of k)} [IsProper g] [GeometricallyReduced g]
    [ConnectedSpace X] (LX : RelativeGroupLaw k g) (σ : SchemeHomOver g f)
    (hσ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t g),
      NeronModelInfra.schemeHomOverComp (LX.mul t x y) σ =
        L.mul t (NeronModelInfra.schemeHomOverComp x σ) (NeronModelInfra.schemeHomOverComp y σ)) :
    ∃ LB : RelativeGroupLaw k (σ.1.imageι ≫ f),
      AbelianSchemePropertyBundle k (σ.1.imageι ≫ f) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (σ.1.imageι ≫ f)),
        LB.mul t x y = LB.mul t y x) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (σ.1.imageι ≫ f)),
        NeronModelInfra.schemeHomOverComp (LB.mul t x y) (⟨σ.1.imageι, rfl⟩ : SchemeHomOver (σ.1.imageι ≫ f) f) =
          L.mul t (NeronModelInfra.schemeHomOverComp x ⟨σ.1.imageι, rfl⟩)
            (NeronModelInfra.schemeHomOverComp y ⟨σ.1.imageι, rfl⟩)) ∧
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra k Ω],
        ∀ z : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) f,
          (∃ b : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) (σ.1.imageι ≫ f),
              NeronModelInfra.schemeHomOverComp b ⟨σ.1.imageι, rfl⟩ = z) ↔
            ∃ y : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) g,
              NeronModelInfra.schemeHomOverComp y σ = z) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism.solution
