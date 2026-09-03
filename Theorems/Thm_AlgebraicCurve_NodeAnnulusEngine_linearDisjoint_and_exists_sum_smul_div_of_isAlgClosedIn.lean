import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_NodeAnnulusEngine_linearDisjoint_and_exists_sum_smul_div_of_isAlgClosedIn

set_option autoImplicit false

theorem AlgebraicCurve.NodeAnnulusEngine.linearDisjoint_and_exists_sum_smul_div_of_isAlgClosedIn
    {k : Type*} [Field k] [CharZero k] {L : Type*} [Field L] [Algebra k L] {F : Type*} [Field F] [Algebra L F] [Algebra k F]
    [IsScalarTower k L F]
    (K : IntermediateField k L) (halg : ∀ y : L, IsAlgebraic ↥K y)
    (FK : IntermediateField k F)
    (hKFK : ∀ y : L, y ∈ K → algebraMap L F y ∈ FK)
    (hgenF : ∀ f : F, ∃ (n : ℕ) (c : Fin n → L) (a : Fin n → F) (m : ℕ) (d : Fin m → L) (b : Fin m → F),
      (∀ i, a i ∈ FK) ∧ (∀ j, b j ∈ FK) ∧ (∑ j, d j • b j) ≠ 0 ∧ f * (∑ j, d j • b j) = ∑ i, c i • a i)

    (hreg : ∀ x : F, x ∈ FK → (∃ p : Polynomial L, p ≠ 0 ∧ (∀ i, p.coeff i ∈ (K : Set L)) ∧
        Polynomial.aeval x (p.map (algebraMap L F)) = 0) → ∃ y : L, y ∈ K ∧ x = algebraMap L F y)
    (C : Subring L) (hCK : ∀ c : L, c ∈ C → c ∈ K)
    (hCfrac : ∀ y : L, y ∈ K → ∃ c d : L, c ∈ C ∧ d ∈ C ∧ d ≠ 0 ∧ y * d = c)
    (𝒩₀ : Subring F) (h𝒩₀ : ∀ a : F, a ∈ 𝒩₀ → a ∈ FK)
    (h𝒩₀frac : ∀ x : F, x ∈ FK → ∃ a b : F, a ∈ 𝒩₀ ∧ b ∈ 𝒩₀ ∧ b ≠ 0 ∧ x * b = a) :
    (∀ (n : ℕ) (c : Fin n → L) (a : Fin n → ↥𝒩₀), LinearIndependent ↥C c →
      ∑ i, c i • ((a i : ↥𝒩₀) : F) = 0 → ∀ i, a i = 0) ∧
    (∀ f : F, ∃ (n : ℕ) (c : Fin n → L) (a : Fin n → ↥𝒩₀) (b : ↥𝒩₀),
      (b : F) ≠ 0 ∧ f * (b : F) = ∑ i, c i • ((a i : ↥𝒩₀) : F)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_NodeAnnulusEngine_linearDisjoint_and_exists_sum_smul_div_of_isAlgClosedIn.solution
