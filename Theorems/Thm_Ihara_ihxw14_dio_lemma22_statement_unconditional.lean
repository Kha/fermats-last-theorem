import Definitions.Def_IharaMennickeCarrier
import P2M.Util
import P2M.Sol.S_Ihara_ihxw14_dio_lemma22_statement_unconditional

set_option autoImplicit false
theorem Ihara.ihxw14_dio_lemma22_statement_unconditional (q : ℕ) [NeZero q] (hq : 2 ≤ q) :
    ∀ m : ℕ, ∀ hmq : Nat.Coprime m q, (q ^ 2 - 1) ∣ m →
      (∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ m → ℓ ∣ (q ^ 2 - 1)) →
      Ihara.mennickeZ q m hmq = ⊤ := by p2m_exact_reverting @_root_.P2MW.S_Ihara_ihxw14_dio_lemma22_statement_unconditional.solution
