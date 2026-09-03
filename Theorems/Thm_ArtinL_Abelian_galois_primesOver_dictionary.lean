import Mathlib
import Definitions.Def_ArtinL_EulerFactor
import Definitions.Def_ArtinL_Abelian
import P2M.Util
import P2M.Sol.S_ArtinL_Abelian_galois_primesOver_dictionary

set_option autoImplicit false

open scoped MatrixGroups
open NumberField

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

open scoped Pointwise Classical
open IsDedekindDomain

theorem ArtinL.Abelian.galois_primesOver_dictionary
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField F] [IsGalois ℚ F]
    (H : Subgroup (F ≃ₐ[ℚ] F)) {p : ℕ} (hp : p.Prime)
    (P : Ideal (𝓞 F)) [P.IsMaximal] [P.LiesOver (Ideal.span {(p : ℤ)})] :
    (∀ v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)),
        ((p : ℕ) : 𝓞 ↥(IntermediateField.fixedField H)) ∈ v.asIdeal →
          ∃ x : F ≃ₐ[ℚ] F, (x • P).under (𝓞 ↥(IntermediateField.fixedField H)) = v.asIdeal) ∧
    (∀ x y : F ≃ₐ[ℚ] F,
        (x • P).under (𝓞 ↥(IntermediateField.fixedField H)) =
            (y • P).under (𝓞 ↥(IntermediateField.fixedField H)) ↔
          ∃ h ∈ H, ∃ d ∈ MulAction.stabilizer (F ≃ₐ[ℚ] F) P, y = h * x * d) ∧
    (∀ (Q : Ideal (𝓞 F)) [Q.IsMaximal] [Q.LiesOver (Ideal.span {(p : ℤ)})]
        (v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H))),
        Q.under (𝓞 ↥(IntermediateField.fixedField H)) = v.asIdeal →
          (Ideal.span {(p : ℤ)}).inertiaDeg' v.asIdeal *
              Nat.card ↥(H ⊓ MulAction.stabilizer (F ≃ₐ[ℚ] F) Q) * Nat.card ↥(Q.inertia (F ≃ₐ[ℚ] F)) =
            Nat.card ↥(MulAction.stabilizer (F ≃ₐ[ℚ] F) Q) * Nat.card ↥(H ⊓ Q.inertia (F ≃ₐ[ℚ] F)) ∧
          ∀ j : ℕ, (∃ σ : F ≃ₐ[ℚ] F, σ ∈ H ∧ σ⁻¹ * arithFrobAt ℤ (F ≃ₐ[ℚ] F) Q ^ j ∈ Q.inertia (F ≃ₐ[ℚ] F)) ↔
            (Ideal.span {(p : ℤ)}).inertiaDeg' v.asIdeal ∣ j) ∧
    (∀ v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)),
        ((p : ℕ) : 𝓞 ↥(IntermediateField.fixedField H)) ∈ v.asIdeal →
          0 < (Ideal.span {(p : ℤ)}).inertiaDeg' v.asIdeal) := by p2m_exact_reverting @_root_.P2MW.S_ArtinL_Abelian_galois_primesOver_dictionary.solution
