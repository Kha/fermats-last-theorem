import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_CuspForm_AdelicLiftGamma1
import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Definitions.Def_LocalNewvector_AdelicSpanCarrier
import Definitions.Def_AutomorphicForm_FnTwist
import Definitions.Def_HeckeCharacter_FiniteOrder
import P2M.Util
import P2M.Sol.S_CuspForm_IsAdelicLiftOf_exists_hasNebentypus_isAdelicLiftOfGamma1_of_mem_span_fnTwist_of_fixed
attribute [-simp] AutomorphicForm.rightTranslationEmbed_smul_apply

set_option autoImplicit false

theorem CuspForm.IsAdelicLiftOf.exists_hasNebentypus_isAdelicLiftOfGamma1_of_mem_span_fnTwist_of_fixed
    {M : ℕ} [NeZero M] {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2}
    {Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ} (hΦg : g.IsAdelicLiftOf Φ)
    (q : ℕ) [Fact q.Prime]
    (η : (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ)ˣ →* ℂˣ)
    (hη : HeckeCharacter.IsFiniteOrderHeckeChar ℚ η)
    (b : ℕ) (hηb : HeckeCharacter.AdmitsModulus ℚ η (AdelicDock.ratLevel (q ^ b)))
    (a : ℕ) (θ : ℤ_[q]ˣ →* ℂˣ)
    (y : LocalNewvector.AdelicSpan (AutomorphicForm.fnTwist ℚ η Φ))
    (hy : y ∈ Submodule.span ℂ
      (Set.range fun x : GL (Fin 2) ℚ_[q] => x • LocalNewvector.AdelicSpan.self (AutomorphicForm.fnTwist ℚ η Φ)))
    (hy₀ : y ≠ 0)
    (hfix : y ∈ LocalNewvector.fixedSubmodule (LocalNewvector.padicK1 q a)
      (LocalNewvector.AdelicSpan (AutomorphicForm.fnTwist ℚ η Φ)))
    (hcent : ∀ u : ℤ_[q]ˣ,
      LocalNewvector.centralGL q (Units.map PadicInt.Coe.ringHom.toMonoidHom u) • y = (θ u : ℂ) • y) :
    ∃ (ε : DirichletCharacter ℂ (q ^ max a 1 * (M / q ^ M.factorization q)))
      (F : CuspForm (CongruenceSubgroup.Gamma1 (q ^ max a 1 * (M / q ^ M.factorization q))) 2),
      F ≠ 0 ∧ CuspForm.HasNebentypus ε F ∧
      (∀ d : ℕ, d.Coprime (q ^ max a 1 * (M / q ^ M.factorization q)) →
        ∀ u : ℤ_[q]ˣ, ((u : ℤ_[q]) : ℚ_[q]) = d →
          ε (d : ZMod (q ^ max a 1 * (M / q ^ M.factorization q))) = ((θ u)⁻¹ : ℂˣ)) ∧
      CuspForm.IsAdelicLiftOfGamma1 F
        (LocalNewvector.AdelicSpan.toFn (AutomorphicForm.fnTwist ℚ η Φ) y).toFn := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_IsAdelicLiftOf_exists_hasNebentypus_isAdelicLiftOfGamma1_of_mem_span_fnTwist_of_fixed.solution
