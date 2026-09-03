import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_MvFormalGroup_PointsV2
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_mvFormalGroup_kernelOfReduction_of_smooth

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM

theorem GoodReductionJacobian.RelativeGroupLaw.exists_mvFormalGroup_kernelOfReduction_of_smooth
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (hL : L.IsCommutative) (hf : Smooth f) :
    ∃ (n : ℕ) (a : Fin n → R), Ideal.span (Set.range a) = ⊤ ∧
      ∀ (i : Fin n) (Rᵢ : Type u) [CommRing Rᵢ] [Algebra R Rᵢ] [IsLocalization.Away (a i) Rᵢ],
        ∃ (g : ℕ) (F : MvFormalGroup g Rᵢ)
          (θ : ∀ (C : Type u) [CommRing C] [Algebra Rᵢ C] (J : Ideal C) [IsAdicComplete J C],
            F.Points C J →
              SchemeHomOver (Spec.map (CommRingCat.ofHom ((algebraMap Rᵢ C).comp (algebraMap R Rᵢ)))) f),
          F.IsComm ∧
          (∀ (C : Type u) [CommRing C] [Algebra Rᵢ C] (J : Ideal C) [IsAdicComplete J C], IsNilpotent J →

            Function.Injective (θ C J) ∧

            (∀ x : F.Points C J,
              (∀ j, x.val j ∈ J) ↔
                Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ (θ C J x).1 =
                  (L.one (Spec.map (CommRingCat.ofHom
                    ((Ideal.Quotient.mk J).comp ((algebraMap Rᵢ C).comp (algebraMap R Rᵢ)))))).1) ∧

            (∀ P : SchemeHomOver (Spec.map (CommRingCat.ofHom ((algebraMap Rᵢ C).comp (algebraMap R Rᵢ)))) f,
              Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ P.1 =
                  (L.one (Spec.map (CommRingCat.ofHom
                    ((Ideal.Quotient.mk J).comp ((algebraMap Rᵢ C).comp (algebraMap R Rᵢ)))))).1 →
                P ∈ Set.range (θ C J)) ∧

            (∀ x y : F.Points C J,
              θ C J (x + y) =
                L.mul (Spec.map (CommRingCat.ofHom ((algebraMap Rᵢ C).comp (algebraMap R Rᵢ))))
                  (θ C J x) (θ C J y)) ∧

            (∀ (C' : Type u) [CommRing C'] [Algebra Rᵢ C'] (J' : Ideal C') [IsAdicComplete J' C'],
              IsNilpotent J' →
                ∀ (φ : C →ₐ[Rᵢ] C') (x : F.Points C J) (x' : F.Points C' J'),
                  (∀ j, x'.val j = φ (x.val j)) →
                    (θ C' J' x').1 = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ (θ C J x).1)) ∧

          (∀ (u : A ⟶ A) (hu : u ≫ f = f),
            (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
              pushPt u hu (L.mul t P Q) = L.mul t (pushPt u hu P) (pushPt u hu Q)) →
            ∃ ρ : MvFormalGroup.End F,
              ∀ (C : Type u) [CommRing C] [Algebra Rᵢ C] (J : Ideal C) [IsAdicComplete J C], IsNilpotent J →
                ∀ x : F.Points C J,
                  θ C J (MvFormalGroup.Hom.evalPoints ρ x) = pushPt u hu (θ C J x)) ∧

          (∀ ρ ρ' : MvFormalGroup.End F,
            (∀ (C : Type u) [CommRing C] [Algebra Rᵢ C] (J : Ideal C) [IsAdicComplete J C], IsNilpotent J →
              ∀ x : F.Points C J,
                MvFormalGroup.Hom.evalPoints ρ x = MvFormalGroup.Hom.evalPoints ρ' x) → ρ = ρ') := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_mvFormalGroup_kernelOfReduction_of_smooth.solution
