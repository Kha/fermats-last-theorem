import Definitions.Def_ModularCurve_SpecializationMap
import P2M.Util
import P2M.Sol.S_ModularCurve_CharPModel_FibreModel_spPic0_compat

theorem ModularCurve.CharPModel.FibreModel.spPic0_compat (N : ℕ) [NeZero N]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (ℓ : ℕ) [Fact ℓ.Prime] (k : Type*)
    [Field k] [CharP k ℓ] (red : A →+* k)
    (fm : ModularCurve.CharPModel.FibreModel N A ℓ k red)
    (hred : Function.Surjective red)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularCurve.ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable)
    (hpres : fm.SpDivPreservesPrincipal hred dataAll hsep) :
    ∀ D : AlgebraicCurve.Divisor.degZero (K := AlgebraicClosure ℚ)
      (F := ModularCurve.modularFunctionFieldBar N),
    ∃ D' : AlgebraicCurve.Divisor.degZero (K := k)
      (F := ModularCurve.modularFunctionFieldC k N),
      (D' : AlgebraicCurve.Divisor k (ModularCurve.modularFunctionFieldC k N))
          = fm.spDiv hred dataAll hsep ↑D ∧
        fm.spPic0 hred dataAll hsep (AlgebraicCurve.Pic0.mk D) = AlgebraicCurve.Pic0.mk D' := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_CharPModel_FibreModel_spPic0_compat.solution
