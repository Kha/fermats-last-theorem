import Definitions.Def_HeckeCharacter_FiniteOrder
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Definitions.Def_AdelicDock_LocalEmbedding
import Mathlib.NumberTheory.Padics.RingHoms
import P2M.Util
import P2M.Sol.S_HeckeCharacter_exists_isFiniteOrderHeckeChar_rat_apply_uniformizerIdele_eq_apply_localUnit_eq_inv

set_option autoImplicit false

theorem HeckeCharacter.exists_isFiniteOrderHeckeChar_rat_apply_uniformizerIdele_eq_apply_localUnit_eq_inv
    (q : ℕ) [Fact q.Prime] (b : ℕ) (χ₀ : (ZMod (q ^ b))ˣ →* ℂˣ) :
    ∃ η : (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ)ˣ →* ℂˣ,
      HeckeCharacter.IsFiniteOrderHeckeChar ℚ η ∧
      HeckeCharacter.AdmitsModulus ℚ η (AdelicDock.ratLevel (q ^ b)) ∧
      AutomorphicForm.IsUnitaryChar (NumberField.RingOfIntegers ℚ) ℚ η ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓq : ℓ ≠ q),
        (η (AutomorphicForm.uniformizerIdele ℚ (@AdelicDock.padicPlace ℓ ⟨hℓ⟩)) : ℂ) =
          χ₀ (ZMod.unitOfCoprime ℓ (((Nat.coprime_primes hℓ (Fact.out : q.Prime)).mpr hℓq).pow_right b))) ∧
      (∀ u : ℤ_[q]ˣ,
        η (Units.map (NumberField.AdelicLevel.finIncl (NumberField.RingOfIntegers ℚ) ℚ)
          (NumberField.AdelicLevel.localUnit (NumberField.RingOfIntegers ℚ) ℚ (AdelicDock.padicPlace q)
            (Units.map (AdelicDock.padicRingEquiv q).toMonoidHom (Units.map PadicInt.Coe.ringHom.toMonoidHom u)))) =
          (χ₀ (Units.map (PadicInt.toZModPow b).toMonoidHom u))⁻¹) ∧
      (∀ x : ℚ_[q]ˣ, (x : ℚ_[q]) = q →
        η (Units.map (NumberField.AdelicLevel.finIncl (NumberField.RingOfIntegers ℚ) ℚ)
          (NumberField.AdelicLevel.localUnit (NumberField.RingOfIntegers ℚ) ℚ (AdelicDock.padicPlace q)
            (Units.map (AdelicDock.padicRingEquiv q).toMonoidHom x))) = 1) := by p2m_exact_reverting @_root_.P2MW.S_HeckeCharacter_exists_isFiniteOrderHeckeChar_rat_apply_uniformizerIdele_eq_apply_localUnit_eq_inv.solution
