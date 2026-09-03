import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_unitPullback_apply_eq_sign_smul_of_ringEquiv_tensor_pin

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme.TwoAffineOpenCover
open scoped TensorProduct

universe u

theorem AlgebraicGeometry.OModulePresheaf.unitPullback_apply_eq_sign_smul_of_ringEquiv_tensor_pin
    {R : Type u} [CommRing R] {Y : Scheme.{u}} (π : Y ⟶ Spec (CommRingCat.of R)) [IsSeparated π]
    (A : Type u) [CommRing A] [Algebra R A]
    (𝒰 𝒱 : Y.OrderedAffineCover)

    (h : pullback π (specMap R A) ⟶ pullback π (specMap R A))
    (hh : h ≫ pullback.snd π (specMap R A) = pullback.snd π (specMap R A))
    (lam : 𝒱.ι → 𝒰.ι) (hl : ∀ v, (𝒱.baseChange π A).U v ≤ h ⁻¹ᵁ (𝒰.baseChange π A).U (lam v))
    (n : ℕ) (z : (OModulePresheaf.unit (pullback.snd π (specMap R A))).cochain (𝒰.baseChange π A) n)
    (s : 𝒱.Idx n) (hinj : Function.Injective (lam ∘ s.1))

    (σ : letI := algebraOfHom π (𝒰.inter ((𝒱.baseChange π A).sortIdx (𝒰.baseChange π A) lam s hinj))
      (A ⊗[R] Γ(Y, 𝒰.inter ((𝒱.baseChange π A).sortIdx (𝒰.baseChange π A) lam s hinj))) ≃+*
        Γ(pullback π (specMap R A), (𝒰.baseChange π A).inter ((𝒱.baseChange π A).sortIdx (𝒰.baseChange π A) lam s hinj)))
    (hσ₁ : letI := algebraOfHom π (𝒰.inter ((𝒱.baseChange π A).sortIdx (𝒰.baseChange π A) lam s hinj))
      ∀ y : Γ(Y, 𝒰.inter ((𝒱.baseChange π A).sortIdx (𝒰.baseChange π A) lam s hinj)),
        σ ((1 : A) ⊗ₜ[R] y) =
          ((pullback π (specMap R A)).presheaf.map
              (homOfLE (𝒰.baseChange_inter_le π A ((𝒱.baseChange π A).sortIdx (𝒰.baseChange π A) lam s hinj))).op).hom
            (((pullback.fst π (specMap R A)).app (𝒰.inter ((𝒱.baseChange π A).sortIdx (𝒰.baseChange π A) lam s hinj))).hom y))
    (hσ₂ : letI := algebraOfHom π (𝒰.inter ((𝒱.baseChange π A).sortIdx (𝒰.baseChange π A) lam s hinj))
      letI := algebraOfHom (pullback.snd π (specMap R A))
        ((𝒰.baseChange π A).inter ((𝒱.baseChange π A).sortIdx (𝒰.baseChange π A) lam s hinj))
      ∀ a : A, σ (a ⊗ₜ[R] (1 : Γ(Y, 𝒰.inter ((𝒱.baseChange π A).sortIdx (𝒰.baseChange π A) lam s hinj)))) =
        algebraMap A Γ(pullback π (specMap R A), (𝒰.baseChange π A).inter ((𝒱.baseChange π A).sortIdx (𝒰.baseChange π A) lam s hinj)) a)
    (σV : letI := algebraOfHom π (𝒱.inter s)
      (A ⊗[R] Γ(Y, 𝒱.inter s)) ≃+* Γ(pullback π (specMap R A), (𝒱.baseChange π A).inter s))
    (hσV₁ : letI := algebraOfHom π (𝒱.inter s)
      ∀ y : Γ(Y, 𝒱.inter s),
        σV ((1 : A) ⊗ₜ[R] y) =
          ((pullback π (specMap R A)).presheaf.map (homOfLE (𝒱.baseChange_inter_le π A s)).op).hom
            (((pullback.fst π (specMap R A)).app (𝒱.inter s)).hom y))
    (hσV₂ : letI := algebraOfHom π (𝒱.inter s)
      letI := algebraOfHom (pullback.snd π (specMap R A)) ((𝒱.baseChange π A).inter s)
      ∀ a : A, σV (a ⊗ₜ[R] (1 : Γ(Y, 𝒱.inter s))) = algebraMap A Γ(pullback π (specMap R A), (𝒱.baseChange π A).inter s) a)

    (θ : letI := algebraOfHom π (𝒰.inter ((𝒱.baseChange π A).sortIdx (𝒰.baseChange π A) lam s hinj))
      letI := algebraOfHom π (𝒱.inter s)
      Γ(Y, 𝒰.inter ((𝒱.baseChange π A).sortIdx (𝒰.baseChange π A) lam s hinj)) →ₐ[R] Γ(Y, 𝒱.inter s))
    (hθ : letI := algebraOfHom π (𝒰.inter ((𝒱.baseChange π A).sortIdx (𝒰.baseChange π A) lam s hinj))
      letI := algebraOfHom π (𝒱.inter s)
      ∀ y : Γ(Y, 𝒰.inter ((𝒱.baseChange π A).sortIdx (𝒰.baseChange π A) lam s hinj)),
        ((pullback π (specMap R A)).presheaf.map
            (homOfLE ((𝒱.baseChange π A).inter_le_preimage_inter_sortIdx h (𝒰.baseChange π A) lam hl s hinj)).op).hom
          ((h.app ((𝒰.baseChange π A).inter ((𝒱.baseChange π A).sortIdx (𝒰.baseChange π A) lam s hinj))).hom
            (((pullback π (specMap R A)).presheaf.map
                (homOfLE (𝒰.baseChange_inter_le π A ((𝒱.baseChange π A).sortIdx (𝒰.baseChange π A) lam s hinj))).op).hom
              (((pullback.fst π (specMap R A)).app (𝒰.inter ((𝒱.baseChange π A).sortIdx (𝒰.baseChange π A) lam s hinj))).hom y))) =
        ((pullback π (specMap R A)).presheaf.map (homOfLE (𝒱.baseChange_inter_le π A s)).op).hom
          (((pullback.fst π (specMap R A)).app (𝒱.inter s)).hom (θ y)))

    (x : letI := algebraOfHom π (𝒰.inter ((𝒱.baseChange π A).sortIdx (𝒰.baseChange π A) lam s hinj))
      A ⊗[R] Γ(Y, 𝒰.inter ((𝒱.baseChange π A).sortIdx (𝒰.baseChange π A) lam s hinj)))
    (hx : σ x = z ((𝒱.baseChange π A).sortIdx (𝒰.baseChange π A) lam s hinj)) :
    letI := algebraOfHom π (𝒰.inter ((𝒱.baseChange π A).sortIdx (𝒰.baseChange π A) lam s hinj))
    letI := algebraOfHom π (𝒱.inter s)
    OModulePresheaf.unitPullback (πX := pullback.snd π (specMap R A)) h (𝒱.baseChange π A) (𝒰.baseChange π A) lam hl n z s =
      ((Equiv.Perm.sign (Tuple.sort (lam ∘ s.1)) : ℤˣ) : ℤ) •
        σV ((Algebra.TensorProduct.map (AlgHom.id A A) θ) x) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_unitPullback_apply_eq_sign_smul_of_ringEquiv_tensor_pin.solution
