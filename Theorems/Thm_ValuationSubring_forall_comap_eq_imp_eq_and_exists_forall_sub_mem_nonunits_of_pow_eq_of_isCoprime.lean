import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_forall_comap_eq_imp_eq_and_exists_forall_sub_mem_nonunits_of_pow_eq_of_isCoprime

set_option autoImplicit false

theorem ValuationSubring.forall_comap_eq_imp_eq_and_exists_forall_sub_mem_nonunits_of_pow_eq_of_isCoprime
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (n : ℕ) (hn : 0 < n) (ζ : F) (hζ : IsPrimitiveRoot ζ n)
    (a : E) (b : F) (hab : a ^ n = algebraMap F E b)
    (hgen : IntermediateField.adjoin F ({a} : Set E) = ⊤)
    (O : ValuationSubring F) [IsDiscreteValuationRing ↥O]
    (ϖ : ↥O) (hϖ : Irreducible ϖ) (u : (↥O)ˣ) (m : ℤ) (hm : IsCoprime m (n : ℤ))
    (hb : b = ((u : ↥O) : F) * ((ϖ : ↥O) : F) ^ m) :

    (∀ O₁ O₂ : ValuationSubring E,
        O₁.comap (algebraMap F E) = O → O₂.comap (algebraMap F E) = O → O₁ = O₂) ∧

    (∃ O' : ValuationSubring E, O'.comap (algebraMap F E) = O ∧
      (∀ e : ↥O', ∃ f : ↥O, (e : E) - algebraMap F E (f : F) ∈ O'.nonunits) ∧
      (∃ (π : ↥O') (v : (↥O')ˣ), Irreducible π ∧
        algebraMap F E ((ϖ : ↥O) : F) = ((v : ↥O') : E) * ((π : ↥O') : E) ^ n)) := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_forall_comap_eq_imp_eq_and_exists_forall_sub_mem_nonunits_of_pow_eq_of_isCoprime.solution
