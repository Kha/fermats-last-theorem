import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import Definitions.Def_Dieudonne_ModpRealization
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_forall_affineOpens_coaction_of_isIso_shear

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

open TensorProduct

theorem GoodReductionJacobian.RelativeGroupLaw.exists_forall_affineOpens_coaction_of_isIso_shear
    (K : Type u) [Field K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    (L : RelativeGroupLaw K f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle K f)
    (n : ℕ) (hfin : IsFinite (L.schemeNsmul n)) (hflat : Flat (L.schemeNsmul n))
    (hsurj : Function.Surjective (L.schemeNsmul n))
    (H : Type u) [CommRing H] [HopfAlgebra K H] [Module.Finite K H] [Coalgebra.IsCocomm K H]
    (e : ∀ (T : Type u) [CommRing T] [Algebra K T],
      WithConv (H →ₐ[K] T) ≃ L.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap K T))) n)
    (he_mul : ∀ (T : Type u) [CommRing T] [Algebra K T] (φ ψ : WithConv (H →ₐ[K] T)),
      ((e T (φ * ψ)).val : SchemeHomOver _ f) = L.mul _ (e T φ).val (e T ψ).val)
    (he_nat : ∀ (T T' : Type u) [CommRing T] [Algebra K T] [CommRing T'] [Algebra K T']
        (g' : T →ₐ[K] T') (φ : WithConv (H →ₐ[K] T)),
      ((e T' (.toConv (g'.comp φ.ofConv))).val : SchemeHomOver _ f).1 =
        Spec.map (CommRingCat.ofHom g'.toRingHom) ≫ (e T φ).val.1)
    (act : pullback f (Spec.map (CommRingCat.ofHom (algebraMap K H))) ⟶ A)
    (hact : act ≫ f = pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H))) ≫ f)
    (hpts : ∀ (T : Type u) [CommRing T] [Algebra K T]
        (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K T))) f) (φ : WithConv (H →ₐ[K] T))
        (hx : x.1 ≫ f = Spec.map (CommRingCat.ofHom (φ.ofConv : H →+* T)) ≫
          Spec.map (CommRingCat.ofHom (algebraMap K H))),
      pullback.lift x.1 (Spec.map (CommRingCat.ofHom (φ.ofConv : H →+* T))) hx ≫ act =
        (L.mul (Spec.map (CommRingCat.ofHom (algebraMap K T))) x (e T φ).val).1)
    (hsh : pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H))) ≫ L.schemeNsmul n = act ≫ L.schemeNsmul n)
    (hiso : IsIso (pullback.lift (f := L.schemeNsmul n) (g := L.schemeNsmul n)
      (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) act hsh))
    :
    letI instK : ∀ V : A.Opens, Algebra K Γ(A, V) := fun V => Scheme.TwoAffineOpenCover.algebraOfHom f V
    ∃ ρ : (∀ U : A.affineOpens, Γ(A, (L.schemeNsmul n) ⁻¹ᵁ (U : A.Opens)) →ₐ[K] Γ(A, (L.schemeNsmul n) ⁻¹ᵁ (U : A.Opens)) ⊗[K] H),
      (∀ (U U' : A.affineOpens) (hle : ((L.schemeNsmul n) ⁻¹ᵁ (U' : A.Opens)) ≤ (L.schemeNsmul n) ⁻¹ᵁ (U : A.Opens))
            (s : Γ(A, (L.schemeNsmul n) ⁻¹ᵁ (U : A.Opens))),
            Algebra.TensorProduct.map (Scheme.TwoAffineOpenCover.restrictAlgHom f hle) (AlgHom.id K H) (ρ U s) =
              ρ U' ((A.presheaf.map (homOfLE hle).op).hom s)) ∧
      (∀ U : A.affineOpens, Function.Injective ((L.schemeNsmul n).app (U : A.Opens)).hom) ∧
      (∀ U : A.affineOpens,
        letI : Algebra Γ(A, (U : A.Opens)) Γ(A, (L.schemeNsmul n) ⁻¹ᵁ (U : A.Opens)) := (((L.schemeNsmul n)).app (U : A.Opens)).hom.toAlgebra
        IsScalarTower K Γ(A, (U : A.Opens)) Γ(A, (L.schemeNsmul n) ⁻¹ᵁ (U : A.Opens)) ∧
          Module.FaithfullyFlat Γ(A, (U : A.Opens)) Γ(A, (L.schemeNsmul n) ⁻¹ᵁ (U : A.Opens))) ∧
      (∀ (U : A.affineOpens) (r : Γ(A, (U : A.Opens))),
        ρ U ((((L.schemeNsmul n)).app (U : A.Opens)).hom r) = (((L.schemeNsmul n)).app (U : A.Opens)).hom r ⊗ₜ[K] (1 : H)) ∧
      (∀ (U : A.affineOpens) (s : Γ(A, (L.schemeNsmul n) ⁻¹ᵁ (U : A.Opens))),
        (Algebra.TensorProduct.rid K K _) (Algebra.TensorProduct.map (AlgHom.id K _) (Bialgebra.counitAlgHom K H) (ρ U s)) = s) ∧
      (∀ (U : A.affineOpens) (s : Γ(A, (L.schemeNsmul n) ⁻¹ᵁ (U : A.Opens))),
        (Algebra.TensorProduct.assoc K K K _ H H) (Algebra.TensorProduct.map (ρ U) (AlgHom.id K H) (ρ U s)) =
          Algebra.TensorProduct.map (AlgHom.id K _) (Bialgebra.comulAlgHom K H) (ρ U s)) ∧
      (∀ U : A.affineOpens,
        letI : Algebra Γ(A, (U : A.Opens)) Γ(A, (L.schemeNsmul n) ⁻¹ᵁ (U : A.Opens)) := (((L.schemeNsmul n)).app (U : A.Opens)).hom.toAlgebra
        ∃ σ : Γ(A, (L.schemeNsmul n) ⁻¹ᵁ (U : A.Opens)) ⊗[Γ(A, (U : A.Opens))] Γ(A, (L.schemeNsmul n) ⁻¹ᵁ (U : A.Opens)) →+*
            Γ(A, (L.schemeNsmul n) ⁻¹ᵁ (U : A.Opens)) ⊗[K] H,
          Function.Bijective σ ∧
          (∀ s, σ (s ⊗ₜ 1) = s ⊗ₜ[K] (1 : H)) ∧ (∀ s, σ (1 ⊗ₜ s) = ρ U s)) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_forall_affineOpens_coaction_of_isIso_shear.solution
