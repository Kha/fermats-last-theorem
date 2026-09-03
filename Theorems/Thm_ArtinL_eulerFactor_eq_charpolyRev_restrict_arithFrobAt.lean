import Mathlib
import Definitions.Def_ArtinL_EulerFactor
import P2M.Util
import P2M.Sol.S_ArtinL_eulerFactor_eq_charpolyRev_restrict_arithFrobAt

set_option autoImplicit false

open scoped MatrixGroups
open NumberField

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

theorem ArtinL.eulerFactor_eq_charpolyRev_restrict_arithFrobAt {n : ℕ} (ρ : Γℚ →* GL (Fin n) ℂ)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField F] [IsGalois ℚ F]
    (ρF : (F ≃ₐ[ℚ] F) →* GL (Fin n) ℂ) (hρ : ρ = ρF.comp (AlgEquiv.restrictNormalHom F))
    {p : ℕ} (hp : p.Prime) (P : Ideal (𝓞 F)) [P.IsMaximal]
    [P.LiesOver (Ideal.span {(p : ℤ)})] :
    ∃ h : ∀ w ∈ Representation.invariants
        ((Deformation.matrixRepresentation ρF).comp (P.inertia (F ≃ₐ[ℚ] F)).subtype),
      Deformation.matrixRepresentation ρF (arithFrobAt ℤ (F ≃ₐ[ℚ] F) P) w ∈
        Representation.invariants
          ((Deformation.matrixRepresentation ρF).comp (P.inertia (F ≃ₐ[ℚ] F)).subtype),
      ArtinL.eulerFactor ρ p =
        ArtinL.charpolyRev
          ((Deformation.matrixRepresentation ρF (arithFrobAt ℤ (F ≃ₐ[ℚ] F) P)).restrict h) := by p2m_exact_reverting @_root_.P2MW.S_ArtinL_eulerFactor_eq_charpolyRev_restrict_arithFrobAt.solution
