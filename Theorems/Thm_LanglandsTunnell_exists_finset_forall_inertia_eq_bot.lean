import Definitions.Def_FrobeniusDensity_DegOneAsymptotic
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.Data.ZMod.QuotientRing
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_exists_finset_forall_inertia_eq_bot

open NumberField Ideal FrobeniusDensity
theorem LanglandsTunnell.exists_finset_forall_inertia_eq_bot
    (L : Type*) [Field L] [NumberField L] :
    ∃ B : Finset ℕ, ∀ ⦃ℓ : ℕ⦄, ℓ.Prime → ℓ ∉ B →
      ∀ (Q : Ideal (𝓞 L)) (_ : Q.IsPrime) (_ : Q.LiesOver (ratPrimeIdeal ℓ)),
        Q.inertia (L ≃ₐ[ℚ] L) = ⊥ := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_exists_finset_forall_inertia_eq_bot.solution
