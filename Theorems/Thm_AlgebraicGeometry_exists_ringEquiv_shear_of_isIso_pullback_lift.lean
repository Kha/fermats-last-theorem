import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import Definitions.Def_Dieudonne_ModpRealization
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_ringEquiv_shear_of_isIso_pullback_lift

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

open TensorProduct

theorem AlgebraicGeometry.exists_ringEquiv_shear_of_isIso_pullback_lift
    (K : Type u) [CommRing K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    (H : Type u) [CommRing H] [Algebra K H]
    (N : A ⟶ A) (hN : N ≫ f = f)
    (act : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ⟶ A) (hact : act ≫ f = (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ≫ f)
    (hsh : (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ≫ N = act ≫ N)
    (hiso : IsIso (pullback.lift (f := N) (g := N) (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) act hsh)) :
    letI instK : ∀ V : A.Opens, Algebra K Γ(A, V) := fun V => Scheme.TwoAffineOpenCover.algebraOfHom f V
    letI instKP : ∀ W : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap K H)))).Opens, Algebra K Γ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap K H)))), W) := fun W =>
      Scheme.TwoAffineOpenCover.algebraOfHom ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ≫ f) W
    ∀ (hNaff : ∀ U : A.affineOpens, IsAffineOpen (N ⁻¹ᵁ (U : A.Opens)))
    (ε : ∀ (V : A.Opens) (_ : IsAffineOpen V), Γ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap K H)))), (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ⁻¹ᵁ V) ≃ₐ[K] Γ(A, V) ⊗[K] H)
    (hε_fst : ∀ (V : A.Opens) (hV : IsAffineOpen V) (a : Γ(A, V)),
      ε V hV (((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))).app V).hom a) = a ⊗ₜ[K] (1 : H))
    (hε_res : ∀ (V V' : A.Opens) (hV : IsAffineOpen V) (hV' : IsAffineOpen V') (hle : V' ≤ V)
        (s : Γ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap K H)))), (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ⁻¹ᵁ V)),
      Algebra.TensorProduct.map (Scheme.TwoAffineOpenCover.restrictAlgHom f hle) (AlgHom.id K H) (ε V hV s) =
        ε V' hV' (((pullback f (Spec.map (CommRingCat.ofHom (algebraMap K H)))).presheaf.map (homOfLE ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))).preimage_mono hle)).op).hom s))
    (hle : ∀ U : A.affineOpens, (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ⁻¹ᵁ (N ⁻¹ᵁ (U : A.Opens)) ≤ act ⁻¹ᵁ (N ⁻¹ᵁ (U : A.Opens)))
    (ρ : ∀ U : A.affineOpens, Γ(A, N ⁻¹ᵁ (U : A.Opens)) →ₐ[K] Γ(A, N ⁻¹ᵁ (U : A.Opens)) ⊗[K] H)
    (hρ : ∀ (U : A.affineOpens) (s : Γ(A, N ⁻¹ᵁ (U : A.Opens))),
      ρ U s = ε (N ⁻¹ᵁ (U : A.Opens)) (hNaff U) ((act.appLE (N ⁻¹ᵁ (U : A.Opens)) ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ⁻¹ᵁ (N ⁻¹ᵁ (U : A.Opens))) (hle U)).hom s))
    (U : A.affineOpens)
    (τ : letI : Algebra Γ(A, (U : A.Opens)) Γ(A, N ⁻¹ᵁ (U : A.Opens)) := ((N).app (U : A.Opens)).hom.toAlgebra
      Γ(pullback N N, (pullback.fst N N) ⁻¹ᵁ (N ⁻¹ᵁ (U : A.Opens))) ≃+*
        Γ(A, N ⁻¹ᵁ (U : A.Opens)) ⊗[Γ(A, (U : A.Opens))] Γ(A, N ⁻¹ᵁ (U : A.Opens)))
    (hle₂ : (pullback.fst N N) ⁻¹ᵁ (N ⁻¹ᵁ (U : A.Opens)) ≤ (pullback.snd N N) ⁻¹ᵁ (N ⁻¹ᵁ (U : A.Opens)))
    (hτ₁ : letI : Algebra Γ(A, (U : A.Opens)) Γ(A, N ⁻¹ᵁ (U : A.Opens)) := ((N).app (U : A.Opens)).hom.toAlgebra
      ∀ s, τ (((pullback.fst N N).app (N ⁻¹ᵁ (U : A.Opens))).hom s) = s ⊗ₜ 1)
    (hτ₂ : letI : Algebra Γ(A, (U : A.Opens)) Γ(A, N ⁻¹ᵁ (U : A.Opens)) := ((N).app (U : A.Opens)).hom.toAlgebra
      ∀ s, τ (((pullback.snd N N).appLE (N ⁻¹ᵁ (U : A.Opens)) ((pullback.fst N N) ⁻¹ᵁ (N ⁻¹ᵁ (U : A.Opens))) hle₂).hom s) = 1 ⊗ₜ s),
    letI : Algebra Γ(A, (U : A.Opens)) Γ(A, N ⁻¹ᵁ (U : A.Opens)) := (N.app (U : A.Opens)).hom.toAlgebra
    ∃ σ : Γ(A, N ⁻¹ᵁ (U : A.Opens)) ⊗[Γ(A, (U : A.Opens))] Γ(A, N ⁻¹ᵁ (U : A.Opens)) →+* Γ(A, N ⁻¹ᵁ (U : A.Opens)) ⊗[K] H,
      Function.Bijective σ ∧ (∀ s, σ (s ⊗ₜ 1) = s ⊗ₜ[K] (1 : H)) ∧ (∀ s, σ (1 ⊗ₜ s) = ρ U s) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_ringEquiv_shear_of_isIso_pullback_lift.solution
