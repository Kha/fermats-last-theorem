import Mathlib
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_GaloisRep_Flat
import P2M.Util
import P2M.Sol.S_ModularCurve_finiteFlatModel_comul_comp_heckeEndo

set_option autoImplicit false
open ModularCurve in
open scoped TensorProduct in

theorem ModularCurve.finiteFlatModel_comul_comp_heckeEndo
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
    (t : HeckeAlg) :
    Coalgebra.comul (R := GaloisRep.ratLocalizedAt p) (A := H) ∘ₗ (φ t).toLinearMap =
        TensorProduct.map (φ t).toLinearMap (φ t).toLinearMap ∘ₗ
          Coalgebra.comul (R := GaloisRep.ratLocalizedAt p) (A := H) ∧
      Coalgebra.counit (R := GaloisRep.ratLocalizedAt p) (A := H) ∘ₗ (φ t).toLinearMap =
        Coalgebra.counit (R := GaloisRep.ratLocalizedAt p) (A := H) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_finiteFlatModel_comul_comp_heckeEndo.solution
