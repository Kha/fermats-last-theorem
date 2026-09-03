import Mathlib
import Definitions.Def_GaloisRep_AdZero
import Definitions.Def_GroupCohomology_TangentSpace
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GaloisRep_LocalFlatClasses
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_ExtCitation_KummerBridge
import P2M.Util
import P2M.Sol.S_ResidualGaloisRep_exists_unipotent_model_dualTwist_of_isLocalRing_baseChange

set_option autoImplicit false

p2m_open "CategoryTheory groupCohomology TrivSqZeroExt ExtCitation~exists_isPrimitiveRoot_smul_eq_pow_cycloChar_localGaloisToGlobal"

theorem ResidualGaloisRep.exists_unipotent_model_dualTwist_of_isLocalRing_baseChange
    {k : Type} [Field k] [Finite k] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) [CharP k p]
    [Algebra ℤ_[p] (ZMod p)] (hker : RingHom.ker (algebraMap ℤ_[p] (ZMod p)) = Ideal.span {(p : ℤ_[p])})
    (ρbar : ResidualGaloisRep k)
    (hconn : ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra ℤ_[p] H),
      Module.Finite ℤ_[p] H ∧ Module.Flat ℤ_[p] H ∧ Coalgebra.IsCocomm ℤ_[p] H ∧
      IsLocalRing (TensorProduct ℤ_[p] (ZMod p) H) ∧
      ∃ e : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p) ≃ ρbar.V × ρbar.V,
        (∀ f g, e (f * g) = e f + e g) ∧
        ∀ (σ : primeLocalGaloisGroup (pPrime p)) (f g : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p)),
          (∀ h : H, g h = ResidualGaloisRep.localAut p σ (f h)) →
            e g = ρbar.dualLiftModuleActAd p 0 σ (e f))
    (ρbar' : ResidualGaloisRep k) (η : ρbar'.V ≃ₗ[k] Module.Dual k ρbar.V)
    (hη : ∀ (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (w : ρbar'.V),
      η (ρbar'.ρ g w) =
        (ZMod.castHom (dvd_refl p) k ((cycloChar p g : (ZMod p)ˣ) : ZMod p)) • ((η w) ∘ₗ (ρbar.ρ g⁻¹))) :
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra ℤ_[p] H),
      Module.Finite ℤ_[p] H ∧ Module.Flat ℤ_[p] H ∧ Coalgebra.IsCocomm ℤ_[p] H ∧
      IsLocalRing (CartierDual (ZMod p) (TensorProduct ℤ_[p] (ZMod p) H)) ∧
      ∃ e : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p) ≃ ρbar'.V × ρbar'.V,
        (∀ f g, e (f * g) = e f + e g) ∧
        ∀ (σ : primeLocalGaloisGroup (pPrime p)) (f g : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p)),
          (∀ h : H, g h = ResidualGaloisRep.localAut p σ (f h)) →
            e g = ρbar'.dualLiftModuleActAd p 0 σ (e f) := by p2m_exact_reverting @_root_.P2MW.S_ResidualGaloisRep_exists_unipotent_model_dualTwist_of_isLocalRing_baseChange.solution
