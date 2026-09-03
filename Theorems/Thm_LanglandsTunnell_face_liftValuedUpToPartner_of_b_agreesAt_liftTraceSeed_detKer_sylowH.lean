import Definitions.Def_AutomorphicForm_HeckeEigensystemMap
import Definitions.Def_AutomorphicForm_ViaCompactCuspNotion
import Definitions.Def_LanglandsTunnell_QuatH
import Definitions.Def_LanglandsTunnell_LiftTraceSeed
import Definitions.Def_LanglandsTunnell_P52Interface
import Definitions.Def_LanglandsTunnell_ExplicitLift
import Definitions.Def_LanglandsTunnell_RealizationDictionary
import Definitions.Def_TaylorWiles_Primes
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_face_liftValuedUpToPartner_of_b_agreesAt_liftTraceSeed_detKer_sylowH

set_option autoImplicit false

theorem LanglandsTunnell.face_liftValuedUpToPartner_of_b_agreesAt_liftTraceSeed_detKer_sylowH
    {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
    (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (Φ : AutomorphicForm.HeckeEigensystem ℚ ℂ) (i : Fin 2)
    {ℓ : ℕ} (hℓ : ℓ.Prime)
    (Q : Ideal (NumberField.RingOfIntegers L)) [Q.IsPrime]
    [Q.LiesOver (FrobeniusDensity.ratPrimeIdeal ℓ)] [Finite (NumberField.RingOfIntegers L ⧸ Q)]
    (hI : Q.inertia (L ≃ₐ[ℚ] L) = ⊥)
    (hE : ∀ w : IsDedekindDomain.HeightOneSpectrum
        (NumberField.RingOfIntegers ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e))),
      w.under (NumberField.RingOfIntegers ℚ) = AutomorphicForm.ratPrime ⟨ℓ, hℓ⟩ →
      (AutomorphicForm.formalBaseChange ℚ ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e)) Φ).b w =
        ((LanglandsTunnell.P2.liftTraceSeed e (LanglandsTunnell.detKer e)).map
          AutomorphicForm.iotaZsqrtdNegTwo).b w)
    (hE₃ : ∀ u : IsDedekindDomain.HeightOneSpectrum
        (NumberField.RingOfIntegers ↥(LanglandsTunnell.fixFld (LanglandsTunnell.sylowH e))),
      u.under (NumberField.RingOfIntegers ℚ) = AutomorphicForm.ratPrime ⟨ℓ, hℓ⟩ →
      (AutomorphicForm.formalBaseChange ℚ ↥(LanglandsTunnell.fixFld (LanglandsTunnell.sylowH e))
            (if i = 0 then Φ else
              Φ.twist fun v => AutomorphicForm.iotaZsqrtdNegTwo (LanglandsTunnell.chiNegThreeWeight v))).a u =
          ((LanglandsTunnell.P2.liftTraceSeed e (LanglandsTunnell.sylowH e)).map
            AutomorphicForm.iotaZsqrtdNegTwo).a u ∧
        (AutomorphicForm.formalBaseChange ℚ ↥(LanglandsTunnell.fixFld (LanglandsTunnell.sylowH e))
            (if i = 0 then Φ else
              Φ.twist fun v => AutomorphicForm.iotaZsqrtdNegTwo (LanglandsTunnell.chiNegThreeWeight v))).b u =
          ((LanglandsTunnell.P2.liftTraceSeed e (LanglandsTunnell.sylowH e)).map
            AutomorphicForm.iotaZsqrtdNegTwo).b u) :
    ∃ M ∈ Submonoid.closure
        ({FLT.ExplicitLift.Slift, FLT.ExplicitLift.Tlift} : Set (Matrix (Fin 2) (Fin 2) (Zsqrtd (-2)))),
      M.map FLT.ExplicitLift.red
          = ((e (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q) : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
              Matrix (Fin 2) (Fin 2) (ZMod 3)) ∧
        (if i = 0 then Φ else
            Φ.twist fun v => AutomorphicForm.iotaZsqrtdNegTwo (LanglandsTunnell.chiNegThreeWeight v)).b
            (AutomorphicForm.ratPrime ⟨ℓ, hℓ⟩) = AutomorphicForm.iotaZsqrtdNegTwo M.det ∧
        ((if i = 0 then Φ else
            Φ.twist fun v => AutomorphicForm.iotaZsqrtdNegTwo (LanglandsTunnell.chiNegThreeWeight v)).a
            (AutomorphicForm.ratPrime ⟨ℓ, hℓ⟩) = AutomorphicForm.iotaZsqrtdNegTwo M.trace ∨
          ((∀ u : IsDedekindDomain.HeightOneSpectrum
                (NumberField.RingOfIntegers ↥(LanglandsTunnell.fixFld (LanglandsTunnell.sylowH e))),
              u.under (NumberField.RingOfIntegers ℚ) = AutomorphicForm.ratPrime ⟨ℓ, hℓ⟩ →
              (u.under (NumberField.RingOfIntegers ℚ)).asIdeal.inertiaDeg' u.asIdeal ≠ 1) ∧
            (if i = 0 then Φ else
            Φ.twist fun v => AutomorphicForm.iotaZsqrtdNegTwo (LanglandsTunnell.chiNegThreeWeight v)).a
              (AutomorphicForm.ratPrime ⟨ℓ, hℓ⟩) = AutomorphicForm.iotaZsqrtdNegTwo (-2 * M.trace))) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_face_liftValuedUpToPartner_of_b_agreesAt_liftTraceSeed_detKer_sylowH.solution
