import Mathlib
import Definitions.Def_GaloisRep_Adic
import P2M.Util
import P2M.Sol.S_GaloisRepAdic_isUnramifiedAt_of_forall_point

set_option autoImplicit false

theorem GaloisRepAdic.isUnramifiedAt_of_forall_point
    {P : Type} [CommRing P] [IsLocalRing P] {ι : Type} {A : ι → Type}
    [∀ i, CommRing (A i)] [∀ i, IsLocalRing (A i)]
    (χ : ∀ i, P →+* A i) (hχ : ∀ i, IsLocalHom (χ i))
    (hinj : ∀ x, (∀ i, χ i x = 0) → x = 0)
    (ρ : GaloisRepAdic P) {q : ℕ}
    (h : ∀ i, (ρ.baseChangeAlong (χ i) (hχ i)).IsUnramifiedAt q) :
    ρ.IsUnramifiedAt q := by p2m_exact_reverting @_root_.P2MW.S_GaloisRepAdic_isUnramifiedAt_of_forall_point.solution
