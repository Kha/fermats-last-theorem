import Definitions.Def_ModularCurve_FullLevelSemistableCoveringTelescope
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringW2
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringGuards
import P2M.Util
import P2M.Sol.S_ModularCurve_FullLevel_SemistableCovering_telescope_laws

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem ModularCurve.FullLevel.SemistableCovering.telescope_laws
    {q : ℕ} [Fact q.Prime] {M' : ℕ} [NeZero M'] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M'))}
    (𝒞 : SemistableCovering q M' A W) (π : A) (hWd : 𝒞.WidthClause π)
    (hG : 𝒞.GenusClause) (hD : 𝒞.DiscFibreClause) (hC : 𝒞.CurveClause) :
      AlgebraicCurve.genusFF (AlgebraicClosure ℚ) ↥(fieldBar q M') + 𝒞.teleN =
        ∑ i : Fin 𝒞.teleN, AlgebraicCurve.genusFF (ResidueField ↥A) (𝒞.teleFbar i) + 𝒞.teleM + 1 ∧
      (∀ i, IsCurveOver (ResidueField ↥A) (𝒞.teleFbar i)) ∧ (∀ i, Algebra.EssFiniteType (ResidueField ↥A) (𝒞.teleFbar i)) ∧
      (∀ i, ∀ Q : Place (ResidueField ↥A) (𝒞.teleFbar i), Q ∉ (𝒞.teleChart i).nodes →
        ∃ (T : ↥(fieldBar q M')) (hT : T ∈ (𝒞.teleChart i).integers),
          (𝒞.teleChart i).residue ⟨T, hT⟩ ≠ 0 ∧ Q.ord ((𝒞.teleChart i).residue ⟨T, hT⟩) = 1 ∧
          (∀ P ∈ (𝒞.teleChart i).dom, (𝒞.teleChart i).placeMap P = Q → T ∈ P.toValuationSubring ∧
            ∃ h : P.evalAt T ∈ A, (⟨P.evalAt T, h⟩ : A) ∈ IsLocalRing.maximalIdeal A) ∧
          ∀ c : A, c ∈ IsLocalRing.maximalIdeal A →
            ∃! P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M'), P ∈ (𝒞.teleChart i).dom ∧ (𝒞.teleChart i).placeMap P = Q ∧ P.evalAt T = c) ∧
      (∀ e, 1 ≤ 𝒞.teleWidth π e ∧ ∃ u : Aˣ, (𝒞.teleAn e).modulus = u * π ^ 𝒞.teleWidth π e) ∧
      (∀ i, HasPrincipalDivisors (ResidueField ↥A) (𝒞.teleFbar i)) ∧
      (∀ i (Q : Place (ResidueField ↥A) (𝒞.teleFbar i)), Q.IsRational) ∧
      (∀ e, (𝒞.teleAn' e).dom = (𝒞.teleAn e).dom ∧ (𝒞.teleAn' e).modulus = (𝒞.teleAn e).modulus ∧
        ((𝒞.teleAn e).modulus : AlgebraicClosure ℚ) ≠ 0 ∧
        (𝒞.teleAn' e).param * (𝒞.teleAn e).param
          = algebraMap (AlgebraicClosure ℚ) (fieldBar q M') ((𝒞.teleAn e).modulus : AlgebraicClosure ℚ)) ∧
      (∀ e, (𝒞.teleAn e).IsAttached (𝒞.teleChart (𝒞.teleSrc e)) (𝒞.teleXs e) ∧ (𝒞.teleAn' e).IsAttached (𝒞.teleChart (𝒞.teleTgt e)) (𝒞.teleXt e)) ∧
      (∀ i, ∀ x ∈ (𝒞.teleChart i).nodes, ∃! e,
        (⟨𝒞.teleSrc e, 𝒞.teleXs e⟩ : Σ j, Place (ResidueField ↥A) (𝒞.teleFbar j)) = ⟨i, x⟩ ∨
        (⟨𝒞.teleTgt e, 𝒞.teleXt e⟩ : Σ j, Place (ResidueField ↥A) (𝒞.teleFbar j)) = ⟨i, x⟩) ∧
      (∀ P : Place (AlgebraicClosure ℚ) (fieldBar q M'),
        (∃ i, P ∈ (𝒞.teleChart i).dom ∧ (∀ j, P ∈ (𝒞.teleChart j).dom → j = i) ∧ ∀ e, P ∉ (𝒞.teleAn e).dom) ∨
        (∃ e, P ∈ (𝒞.teleAn e).dom ∧ (∀ e', P ∈ (𝒞.teleAn e').dom → e' = e) ∧ ∀ i, P ∉ (𝒞.teleChart i).dom)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_FullLevel_SemistableCovering_telescope_laws.solution
