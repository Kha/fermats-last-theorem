import Mathlib
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_GaloisRep_Flat
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_bialgHom_surjective_model_submodule_heckeTorsion_jZero

set_option autoImplicit false
open ModularCurve in

theorem ModularCurve.exists_bialgHom_surjective_model_submodule_heckeTorsion_jZero
    (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime] (𝔪 : Ideal HeckeAlg)
    (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt p) H]
    [Module.Finite (GaloisRep.ratLocalizedAt p) H] [Module.Flat (GaloisRep.ratLocalizedAt p) H]
    [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H]
    (e : letI := heckeModuleBar N
      WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃ ↥(heckeTorsion (JZero N) 𝔪))
    (he_add : letI := heckeModuleBar N
      ∀ f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ), e (f * g) = e f + e g)
    (he_gal : letI := heckeModuleBar N
      ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
        (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
        (∀ h : H, g h = σ (f h)) →
          ((e g : ↥(heckeTorsion (JZero N) 𝔪)) : JZero N) = σ • ((e f : ↥(heckeTorsion (JZero N) 𝔪)) : JZero N))
    (φ : HeckeAlg → (H →ₐ[GaloisRep.ratLocalizedAt p] H))
    (hφ : letI := heckeModuleBar N
      ∀ (t : HeckeAlg) (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
        (∀ h : H, g h = f (φ t h)) → ((e g : ↥(heckeTorsion (JZero N) 𝔪)) : JZero N) = t • ((e f : ↥(heckeTorsion (JZero N) 𝔪)) : JZero N))
    (hsmc : letI := heckeModuleBar N
      SMulCommClass (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) HeckeAlg (JZero N))
    (V : letI := heckeModuleBar N; Submodule (HeckeAlg ⧸ 𝔪) ↥(heckeTorsion (JZero N) 𝔪))
    (hV : letI := heckeModuleBar N; haveI := hsmc
      ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (v : ↥(heckeTorsion (JZero N) 𝔪)),
        v ∈ V → mTorsionGaloisRep (JZero N) 𝔪 σ v ∈ V) :
    letI := heckeModuleBar N
    ∃ (HV : Type) (_ : CommRing HV) (_ : HopfAlgebra (GaloisRep.ratLocalizedAt p) HV)
      (_ : Module.Finite (GaloisRep.ratLocalizedAt p) HV)
      (_ : Module.Free (GaloisRep.ratLocalizedAt p) HV)
      (_ : Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) HV)
      (π : H →ₐc[GaloisRep.ratLocalizedAt p] HV)
      (eV : WithConv (HV →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃ ↥V)
      (φV : HeckeAlg → (HV →ₐ[GaloisRep.ratLocalizedAt p] HV)),
      Function.Surjective π ∧
      (∀ f : WithConv (HV →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
        ((eV f : ↥V) : ↥(heckeTorsion (JZero N) 𝔪)) =
          e (WithConv.toConv
            ((WithConv.ofConv f).comp (π : H →ₐ[GaloisRep.ratLocalizedAt p] HV)))) ∧
      (∀ t : HeckeAlg,
        (φV t).comp (π : H →ₐ[GaloisRep.ratLocalizedAt p] HV) =
          (π : H →ₐ[GaloisRep.ratLocalizedAt p] HV).comp (φ t)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_bialgHom_surjective_model_submodule_heckeTorsion_jZero.solution
