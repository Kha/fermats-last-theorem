import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import Definitions.Def_Dieudonne_ModpRealization
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_linearMap_primitives_ker_d_one_and_lifts_of_forall_affineOpens_coaction
attribute [-simp] RegularLocalRingQuotientAscent.dualNumberFst_apply

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct

universe u

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.exists_linearMap_primitives_ker_d_one_and_lifts_of_forall_affineOpens_coaction
    (K : Type u) [Field K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    (hA : AbelianSchemePropertyBundle K f) (N : A ⟶ A) (hN : N ≫ f = f)
    (H : Type u) [CommRing H] [HopfAlgebra K H] :
    letI instK : ∀ V : A.Opens, Algebra K Γ(A, V) := fun V => Scheme.TwoAffineOpenCover.algebraOfHom f V
    ∀ (ρ : ∀ U : A.affineOpens, Γ(A, N ⁻¹ᵁ (U : A.Opens)) →ₐ[K] Γ(A, N ⁻¹ᵁ (U : A.Opens)) ⊗[K] H)
      (hnat : ∀ (U U' : A.affineOpens) (hle : (N ⁻¹ᵁ (U' : A.Opens)) ≤ N ⁻¹ᵁ (U : A.Opens))
          (s : Γ(A, N ⁻¹ᵁ (U : A.Opens))),
          Algebra.TensorProduct.map (Scheme.TwoAffineOpenCover.restrictAlgHom f hle) (AlgHom.id K H) (ρ U s) =
            ρ U' ((A.presheaf.map (homOfLE hle).op).hom s))
      (hinj : ∀ U : A.affineOpens, Function.Injective (N.app (U : A.Opens)).hom)
      (hρN : ∀ (U : A.affineOpens) (r : Γ(A, (U : A.Opens))),
          ρ U ((N.app (U : A.Opens)).hom r) = (N.app (U : A.Opens)).hom r ⊗ₜ[K] (1 : H))
      (hcoinv : ∀ (U : A.affineOpens) (s : Γ(A, N ⁻¹ᵁ (U : A.Opens))),
          ρ U s = s ⊗ₜ[K] (1 : H) → s ∈ Set.range (N.app (U : A.Opens)).hom)
      (hlift : ∀ (U : A.affineOpens) (h : H), h ∈ primitives K H →
          ∃ s : Γ(A, N ⁻¹ᵁ (U : A.Opens)), ρ U s = s ⊗ₜ[K] (1 : H) + (1 : Γ(A, N ⁻¹ᵁ (U : A.Opens))) ⊗ₜ[K] h)
      (𝒦 : A.OrderedAffineCover),
    ∃ (θ : ↥(primitives K H) →ₗ[K] ↥(LinearMap.ker ((OModulePresheaf.unit f).d 𝒦 1)))
      (s : ↥(primitives K H) → ∀ i : 𝒦.ι, Γ(A, N ⁻¹ᵁ 𝒦.U i)),

      (∀ (x : ↥(primitives K H)) (i : 𝒦.ι),
        ρ ⟨𝒦.U i, 𝒦.isAffineOpen i⟩ (s x i) = s x i ⊗ₜ[K] (1 : H) + (1 : Γ(A, N ⁻¹ᵁ 𝒦.U i)) ⊗ₜ[K] (x : H)) ∧

      (∀ (x : ↥(primitives K H)) (t : 𝒦.Idx 1),
        (N.app (𝒦.inter t)).hom
            ((θ x : ↥(LinearMap.ker ((OModulePresheaf.unit f).d 𝒦 1))).1 t) =
          (A.presheaf.map (homOfLE (N.preimage_mono (𝒦.inter_le t 0))).op).hom (s x (t.1 0)) -
            (A.presheaf.map (homOfLE (N.preimage_mono (𝒦.inter_le t 1))).op).hom (s x (t.1 1))) ∧

      (∀ x : ↥(primitives K H),
        ((θ x : ↥(LinearMap.ker ((OModulePresheaf.unit f).d 𝒦 1))) : (OModulePresheaf.unit f).cochain 𝒦 1) ∈
          LinearMap.range ((OModulePresheaf.unit f).d 𝒦 0) → x = 0) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_linearMap_primitives_ker_d_one_and_lifts_of_forall_affineOpens_coaction.solution
