import Definitions.Def_ModularCurve_SpecializationMap
import P2M.Util
import P2M.Sol.S_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_finChart_mem_nonunits_iff

open AlgebraicCurve ModularCurve CharPModel

theorem ModularCurve.CharPModel.FibreModel.place_eq_of_forall_finChart_mem_nonunits_iff
    (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (k : Type*) [Field k] [CharP k ℓ] (red : A →+* k)
    (fm : ModularCurve.CharPModel.FibreModel N A ℓ k red)
    (hred : Function.Surjective red)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularCurve.ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable)
    (v₁ v₂ : Place k (modularFunctionFieldC k N))
    (hj₁ : (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N)
      ∈ v₁.toValuationSubring)
    (hj₂ : (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N)
      ∈ v₂.toValuationSubring)
    (hFin : ∀ b : fm.BFin,
      ((fm.piFin b : modularFunctionFieldC k N) ∈ v₁.toValuationSubring.nonunits ↔
        (fm.piFin b : modularFunctionFieldC k N) ∈ v₂.toValuationSubring.nonunits)) :
    v₁ = v₂ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_finChart_mem_nonunits_iff.solution
