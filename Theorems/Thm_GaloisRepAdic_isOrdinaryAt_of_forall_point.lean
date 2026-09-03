import Definitions.Def_GaloisRep_LocalConditions
import P2M.Util
import P2M.Sol.S_GaloisRepAdic_isOrdinaryAt_of_forall_point

open scoped TensorProduct
theorem GaloisRepAdic.isOrdinaryAt_of_forall_point
    {P : Type} [CommRing P] [IsLocalRing P]
    {n : ℕ} {A : Fin n → Type} [∀ i, CommRing (A i)] [∀ i, IsLocalRing (A i)]
    (χ : ∀ i, P →+* A i) (hχ : ∀ i, IsLocalHom (χ i))
    (hinj : ∀ x : P, (∀ i, χ i x = 0) → x = 0)
    (ρ : GaloisRepAdic P) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hdet : ρ.DetIsCyclotomic p)
    (hord : ∀ i, (ρ.baseChangeAlong (χ i) (hχ i)).IsOrdinaryAt p) :
    ρ.IsOrdinaryAt p := by p2m_exact_reverting @_root_.P2MW.S_GaloisRepAdic_isOrdinaryAt_of_forall_point.solution
