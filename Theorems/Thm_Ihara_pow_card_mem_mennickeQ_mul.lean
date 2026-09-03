import Definitions.Def_IharaMennickeCarrier
import Definitions.Def_SchurMultiplierTrivial
import P2M.Util
import P2M.Sol.S_Ihara_pow_card_mem_mennickeQ_mul

open scoped MatrixGroups
theorem Ihara.pow_card_mem_mennickeQ_mul (q : ℕ) [NeZero q] (m' m₅ m₆ : ℕ) [NeZero m']
    [NeZero m₅] [NeZero m₆] (hcop : Nat.Coprime m' (m₅ * m₆)) (h56 : Nat.Coprime m₅ m₆)
    (hm'q : Nat.Coprime m' q) (hm''q : Nat.Coprime (m₅ * m₆) q)
    (hmq : Nat.Coprime (m' * (m₅ * m₆)) q) (hm'n : Nat.Coprime m' (q ^ 2 - 1))
    (hsat : (q ^ 2 - 1) ∣ m₅ * m₆) (h5 : ∀ p : ℕ, p.Prime → p ∣ m₅ → 5 ≤ p)
    (hP1 : ∀ p n : ℕ, p.Prime → 5 ≤ p → n ≠ 0 → commutator (SL(2, ZMod (p ^ n))) = ⊤)
    (hP2 : ∀ p n : ℕ, p.Prime → 5 ≤ p → n ≠ 0 →
      Ihara.HasTrivialSchurMultiplier (SL(2, ZMod (p ^ n))))
    (hN' : Ihara.MennickeCSP m' q hm'q)
    (hsurj' : Function.Surjective (Ihara.slAwayReduction m' q hm'q))
    (hZ'' : Ihara.mennickeZ q (m₅ * m₆) hm''q = ⊤)
    (hhabel'' : Ihara.principalCongruenceAway (m₅ * m₆) q hm''q ≤
      commutator (SL(2, Ihara.ZAway q)) ⊔ Ihara.mennickeQ q (m₅ * m₆))
    (hsurj'' : Function.Surjective (Ihara.slAwayReduction (m₅ * m₆) q hm''q))
    {x : SL(2, Ihara.ZAway q)}
    (hx : x ∈ Ihara.principalCongruenceAway (m' * (m₅ * m₆)) q hmq) :
    x ^ Nat.card (SL(2, ZMod m₆)) ∈ Ihara.mennickeQ q (m' * (m₅ * m₆)) := by p2m_exact_reverting @_root_.P2MW.S_Ihara_pow_card_mem_mennickeQ_mul.solution
