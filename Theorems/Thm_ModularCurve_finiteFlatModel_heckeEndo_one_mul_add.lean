import Mathlib
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_GaloisRep_Flat
import P2M.Util
import P2M.Sol.S_ModularCurve_finiteFlatModel_heckeEndo_one_mul_add

set_option autoImplicit false
open ModularCurve in
open scoped TensorProduct in

theorem ModularCurve.finiteFlatModel_heckeEndo_one_mul_add
    (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime] (𝔪 : Ideal HeckeAlg)
    (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt p) H]
    [Module.Finite (GaloisRep.ratLocalizedAt p) H] [Module.Flat (GaloisRep.ratLocalizedAt p) H]
    (e : letI := heckeModuleBar N
      WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃ ↥(heckeTorsion (JZero N) 𝔪))
    (he_add : letI := heckeModuleBar N
      ∀ f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ), e (f * g) = e f + e g)
    (φ : HeckeAlg → (H →ₐ[GaloisRep.ratLocalizedAt p] H))
    (hφ : letI := heckeModuleBar N
      ∀ (t : HeckeAlg) (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
        (∀ h : H, g h = f (φ t h)) → ((e g : ↥(heckeTorsion (JZero N) 𝔪)) : JZero N) = t • ((e f : ↥(heckeTorsion (JZero N) 𝔪)) : JZero N))
    (t₁ t₂ : HeckeAlg) :
    φ 1 = AlgHom.id (GaloisRep.ratLocalizedAt p) H ∧
      φ (t₁ * t₂) = (φ t₁).comp (φ t₂) ∧
      (φ (t₁ + t₂)).toLinearMap =
        LinearMap.mul' (GaloisRep.ratLocalizedAt p) H ∘ₗ
          TensorProduct.map (φ t₁).toLinearMap (φ t₂).toLinearMap ∘ₗ
            Coalgebra.comul (R := GaloisRep.ratLocalizedAt p) (A := H) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_finiteFlatModel_heckeEndo_one_mul_add.solution
