import Mathlib
import Definitions.Def_GaloisRep_ConditionLifts
import Definitions.Def_Deformations_ProartinianCompact
import P2M.Util
import P2M.Sol.S_GaloisRep_residual_framed_isEquiv_baseChangeAlong

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits IsLocalRing Deformation Deformation.ProartinianCat
theorem GaloisRep.residual_framed_isEquiv_baseChangeAlong
    (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪]
    (ρbar : ResidualGaloisRep (IsLocalRing.ResidueField 𝒪))
    (ρ₀ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →ₜ* GL (Fin 2) (Deformation.ProartinianCat.residueField (𝓞 := 𝒪)))
    (b : Module.Basis (Fin 2) (IsLocalRing.ResidueField 𝒪) ρbar.V)
    (hρ₀ : ∀ σ, (ρ₀ σ).val = LinearMap.toMatrix b b (ρbar.ρ σ))
    {R : Deformation.ProartinianCat 𝒪}
    (ρu : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →ₜ* GL (Fin 2) R)
    (hρu : ρu ∈ (Deformation.liftFunctor (Fin 2) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) 𝒪 ρ₀).obj R)
    (hcont : GaloisActionIsAdicContinuous R
      ((Units.coeHom _).comp (Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp ρu.toMonoidHom))) :
    ({ V := Fin 2 → R, finrank_eq := by simp,
       ρ := (Units.coeHom _).comp (Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp ρu.toMonoidHom),
       isAdicContinuous := hcont } : GaloisRepAdic R).residual.IsEquiv
      (ρbar.baseChangeAlong (IsLocalRing.ResidueField.map (algebraMap 𝒪 R))) := by p2m_exact_reverting @_root_.P2MW.S_GaloisRep_residual_framed_isEquiv_baseChangeAlong.solution
