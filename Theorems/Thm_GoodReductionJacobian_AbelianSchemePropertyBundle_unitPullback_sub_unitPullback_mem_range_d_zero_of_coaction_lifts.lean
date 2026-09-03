import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_AbelianSchemePropertyBundle_unitPullback_sub_unitPullback_mem_range_d_zero_of_coaction_lifts

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct

universe u

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.unitPullback_sub_unitPullback_mem_range_d_zero_of_coaction_lifts
    (K : Type u) [Field K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    (hA : AbelianSchemePropertyBundle K f) (N : A ⟶ A) (hN : N ≫ f = f)
    (H : Type u) [CommRing H] [Algebra K H] :
    letI instK : ∀ V : A.Opens, Algebra K Γ(A, V) := fun V => Scheme.TwoAffineOpenCover.algebraOfHom f V
    ∀ (ρ : ∀ U : A.affineOpens, Γ(A, N ⁻¹ᵁ (U : A.Opens)) →ₐ[K] Γ(A, N ⁻¹ᵁ (U : A.Opens)) ⊗[K] H)
      (hnat : ∀ (U U' : A.affineOpens) (hle : (N ⁻¹ᵁ (U' : A.Opens)) ≤ N ⁻¹ᵁ (U : A.Opens))
          (s : Γ(A, N ⁻¹ᵁ (U : A.Opens))),
          Algebra.TensorProduct.map (Scheme.TwoAffineOpenCover.restrictAlgHom f hle) (AlgHom.id K H) (ρ U s) =
            ρ U' ((A.presheaf.map (homOfLE hle).op).hom s))
      (hinj : ∀ U : A.affineOpens, Function.Injective (N.app (U : A.Opens)).hom)
      (hcoinv : ∀ (U : A.affineOpens) (s : Γ(A, N ⁻¹ᵁ (U : A.Opens))),
          ρ U s = s ⊗ₜ[K] (1 : H) → s ∈ Set.range (N.app (U : A.Opens)).hom)

      (φ : A ⟶ A) (hφN : φ ≫ N = N ≫ φ) (φH : H →ₐ[K] H)
      (hequiv : ∀ (U W : A.affineOpens) (hle : N ⁻¹ᵁ (W : A.Opens) ≤ φ ⁻¹ᵁ (N ⁻¹ᵁ (U : A.Opens))),
        ∃ Ξ : Γ(A, N ⁻¹ᵁ (U : A.Opens)) ⊗[K] H →+* Γ(A, N ⁻¹ᵁ (W : A.Opens)) ⊗[K] H,
          (∀ s : Γ(A, N ⁻¹ᵁ (U : A.Opens)),
              Ξ (s ⊗ₜ[K] (1 : H)) = (φ.appLE (N ⁻¹ᵁ (U : A.Opens)) (N ⁻¹ᵁ (W : A.Opens)) hle).hom s ⊗ₜ[K] (1 : H)) ∧
          (∀ x : H, Ξ ((1 : Γ(A, N ⁻¹ᵁ (U : A.Opens))) ⊗ₜ[K] x) = (1 : Γ(A, N ⁻¹ᵁ (W : A.Opens))) ⊗ₜ[K] φH x) ∧
          (∀ s : Γ(A, N ⁻¹ᵁ (U : A.Opens)),
              Ξ (ρ U s) = ρ W ((φ.appLE (N ⁻¹ᵁ (U : A.Opens)) (N ⁻¹ᵁ (W : A.Opens)) hle).hom s)))

      (𝒦 𝒲 : A.OrderedAffineCover) (lam lam' : 𝒲.ι → 𝒦.ι)
      (hlam : ∀ w, 𝒲.U w ≤ φ ⁻¹ᵁ 𝒦.U (lam w)) (hlam' : ∀ w, 𝒲.U w ≤ (𝟙 A) ⁻¹ᵁ 𝒦.U (lam' w))

      (h h' : H) (hh' : φH h = h')
      (S S' : ∀ i : 𝒦.ι, Γ(A, N ⁻¹ᵁ 𝒦.U i))
      (hS : ∀ i : 𝒦.ι, ρ ⟨𝒦.U i, 𝒦.isAffineOpen i⟩ (S i) = S i ⊗ₜ[K] (1 : H) + (1 : Γ(A, N ⁻¹ᵁ 𝒦.U i)) ⊗ₜ[K] h)
      (hS' : ∀ i : 𝒦.ι, ρ ⟨𝒦.U i, 𝒦.isAffineOpen i⟩ (S' i) = S' i ⊗ₜ[K] (1 : H) + (1 : Γ(A, N ⁻¹ᵁ 𝒦.U i)) ⊗ₜ[K] h')
      (c c' : (OModulePresheaf.unit f).cochain 𝒦 1)
      (hc : ∀ t : 𝒦.Idx 1, (N.app (𝒦.inter t)).hom (c t) =
        (A.presheaf.map (homOfLE (N.preimage_mono (𝒦.inter_le t 0))).op).hom (S (t.1 0)) -
          (A.presheaf.map (homOfLE (N.preimage_mono (𝒦.inter_le t 1))).op).hom (S (t.1 1)))
      (hc' : ∀ t : 𝒦.Idx 1, (N.app (𝒦.inter t)).hom (c' t) =
        (A.presheaf.map (homOfLE (N.preimage_mono (𝒦.inter_le t 0))).op).hom (S' (t.1 0)) -
          (A.presheaf.map (homOfLE (N.preimage_mono (𝒦.inter_le t 1))).op).hom (S' (t.1 1))),
    OModulePresheaf.unitPullback (πX := f) φ 𝒲 𝒦 lam hlam 1 c -
        OModulePresheaf.unitPullback (πX := f) (𝟙 A) 𝒲 𝒦 lam' hlam' 1 c' ∈
      LinearMap.range ((OModulePresheaf.unit f).d 𝒲 0) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_unitPullback_sub_unitPullback_mem_range_d_zero_of_coaction_lifts.solution
