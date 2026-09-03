import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_IsAffineOpen_ringEquiv_tensor_map_eq_map_app_of_specMap_comp_fromSpec_eq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing TensorProduct Scheme.TwoAffineOpenCover

universe u

theorem AlgebraicGeometry.IsAffineOpen.ringEquiv_tensor_map_eq_map_app_of_specMap_comp_fromSpec_eq
    {T' : Type u} [CommRing T'] [IsLocalRing T']
    {Y Y' Ak Xk : Scheme.{u}} (qY : Y ⟶ Spec (CommRingCat.of T')) (qY' : Y' ⟶ Spec (CommRingCat.of T'))
    (fk : Ak ⟶ Spec (CommRingCat.of (ResidueField T'))) (fXk : Xk ⟶ Spec (CommRingCat.of (ResidueField T')))
    (hk : Xk ⟶ Ak) (hhkf : hk ≫ fk = fXk)
    (OU : Y.Opens) (hOU : IsAffineOpen OU) (OU' : Y'.Opens) (hOU' : IsAffineOpen OU')
    (W : Ak.Opens) (W' : Xk.Opens) (hW : IsAffineOpen W) (hW' : IsAffineOpen W') (hWW : W' ≤ hk ⁻¹ᵁ W)
    (m : (W : Scheme.{u}) ⟶ Y)
    (h : letI := algebraOfHom qY OU; letI := algebraOfHom qY' OU'
      Γ(Y, OU) →ₐ[T'] Γ(Y', OU'))
    (σ : letI := algebraOfHom qY OU
      (ResidueField T') ⊗[T'] Γ(Y, OU) ≃+* Γ(Ak, W))
    (σ' : letI := algebraOfHom qY' OU'
      (ResidueField T') ⊗[T'] Γ(Y', OU') ≃+* Γ(Xk, W'))
    (hσ₁ : letI := algebraOfHom qY OU
      hW.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom σ.toRingHom) ≫
          Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.includeRight : Γ(Y, OU) →ₐ[T'] (ResidueField T') ⊗[T'] Γ(Y, OU)).toRingHom) ≫
          hOU.fromSpec = m)
    (hσ₂ : letI := algebraOfHom qY OU
      letI := algebraOfHom fk W
      ∀ x : ResidueField T', σ (x ⊗ₜ[T'] (1 : Γ(Y, OU))) = algebraMap (ResidueField T') Γ(Ak, W) x)
    (hσ'₂ : letI := algebraOfHom qY' OU'
      letI := algebraOfHom fXk W'
      ∀ x : ResidueField T', σ' (x ⊗ₜ[T'] (1 : Γ(Y', OU'))) = algebraMap (ResidueField T') Γ(Xk, W') x)
    (hcomp : letI := algebraOfHom qY OU
      letI := algebraOfHom qY' OU'
      hW'.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom σ'.toRingHom) ≫
          Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.includeRight : Γ(Y', OU') →ₐ[T'] (ResidueField T') ⊗[T'] Γ(Y', OU')).toRingHom) ≫
          Spec.map (CommRingCat.ofHom h.toRingHom) ≫ hOU.fromSpec = Xk.homOfLE hWW ≫ (hk ∣_ W) ≫ m) :
    letI := algebraOfHom qY OU
    letI := algebraOfHom qY' OU'
    ∀ z : (ResidueField T') ⊗[T'] Γ(Y, OU),
      σ' (Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T')) h z) =
        (Xk.presheaf.map (homOfLE hWW).op).hom ((hk.app W).hom (σ z)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_IsAffineOpen_ringEquiv_tensor_map_eq_map_app_of_specMap_comp_fromSpec_eq.solution
