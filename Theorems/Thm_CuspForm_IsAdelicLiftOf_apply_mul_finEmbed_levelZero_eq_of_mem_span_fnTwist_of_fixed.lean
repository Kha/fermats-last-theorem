import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_LocalNewvector_AdelicSpanCarrier
import Definitions.Def_AutomorphicForm_FnTwist
import Definitions.Def_HeckeCharacter_FiniteOrder
import P2M.Util
import P2M.Sol.S_CuspForm_IsAdelicLiftOf_apply_mul_finEmbed_levelZero_eq_of_mem_span_fnTwist_of_fixed
attribute [-simp] AutomorphicForm.rightTranslationEmbed_smul_apply

set_option autoImplicit false

theorem CuspForm.IsAdelicLiftOf.apply_mul_finEmbed_levelZero_eq_of_mem_span_fnTwist_of_fixed
    {M : ℕ} [NeZero M] {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2}
    {Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ} (hΦg : g.IsAdelicLiftOf Φ)
    (q : ℕ) [Fact q.Prime]
    (η : (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ)ˣ →* ℂˣ)
    (hη : AutomorphicForm.IsIdeleClassChar (NumberField.RingOfIntegers ℚ) ℚ η)
    (b : ℕ) (hηb : HeckeCharacter.AdmitsModulus ℚ η (AdelicDock.ratLevel (q ^ b)))
    (a : ℕ) (θ : ℤ_[q]ˣ →* ℂˣ)
    (y : LocalNewvector.AdelicSpan (AutomorphicForm.fnTwist ℚ η Φ))
    (hy : y ∈ Submodule.span ℂ
      (Set.range fun x : GL (Fin 2) ℚ_[q] => x • LocalNewvector.AdelicSpan.self (AutomorphicForm.fnTwist ℚ η Φ)))
    (hfix : y ∈ LocalNewvector.fixedSubmodule (LocalNewvector.padicK1 q a)
      (LocalNewvector.AdelicSpan (AutomorphicForm.fnTwist ℚ η Φ)))
    (hcent : ∀ u : ℤ_[q]ˣ,
      LocalNewvector.centralGL q (Units.map PadicInt.Coe.ringHom.toMonoidHom u) • y = (θ u : ℂ) • y) :
    (∀ (γ : GL (Fin 2) ℚ) (z : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ),
        (LocalNewvector.AdelicSpan.toFn (AutomorphicForm.fnTwist ℚ η Φ) y).toFn
            (AutomorphicForm.globalPoints (NumberField.RingOfIntegers ℚ) ℚ γ * z) =
          (LocalNewvector.AdelicSpan.toFn (AutomorphicForm.fnTwist ℚ η Φ) y).toFn z) ∧
    ∀ u ∈ NumberField.AdelicLevel.finiteLevelZero (NumberField.RingOfIntegers ℚ) ℚ
        (AdelicDock.ratLevel (q ^ max a 1 * (M / q ^ M.factorization q))),
      ∀ d : ℤ_[q]ˣ,
        Valued.v
            (((u : Matrix (Fin 2) (Fin 2)
                (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ)) 1 1)
                (AdelicDock.padicPlace q) -
              AdelicDock.padicRingEquiv q ((d : ℤ_[q]) : ℚ_[q])) ≤
          NumberField.AdelicLevel.idealBound (NumberField.RingOfIntegers ℚ)
            (AdelicDock.ratLevel (q ^ max a 1 * (M / q ^ M.factorization q))) (AdelicDock.padicPlace q) →
        ∀ z : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ,
          (LocalNewvector.AdelicSpan.toFn (AutomorphicForm.fnTwist ℚ η Φ) y).toFn
              (z * AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ u) =
            (θ d : ℂ) * (LocalNewvector.AdelicSpan.toFn (AutomorphicForm.fnTwist ℚ η Φ) y).toFn z := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_IsAdelicLiftOf_apply_mul_finEmbed_levelZero_eq_of_mem_span_fnTwist_of_fixed.solution
