import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_zmod_prod_equiv_of_natCard_nsmul_eq_one_eq_sq

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.exists_zmod_prod_equiv_of_natCard_nsmul_eq_one_eq_sq
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (hc : L.IsCommutative)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (H : Set (SchemeHomOver t f)) (hfin : H.Finite)
    (hone : L.one t ∈ H) (hmul : ∀ P Q : SchemeHomOver t f, P ∈ H → Q ∈ H → L.mul t P Q ∈ H)
    (hinv : ∀ P : SchemeHomOver t f, P ∈ H → L.inv t P ∈ H)
    (N : ℕ) [NeZero N] (hN : ∀ P : SchemeHomOver t f, P ∈ H → L.nsmul t N P = L.one t)
    (hcard : ∀ d : ℕ, d ∣ N → Nat.card {P : ↥H // L.nsmul t d P.1 = L.one t} = d ^ 2) :
    ∃ e : ZMod N × ZMod N ≃ ↥H,
      ∀ x y : ZMod N × ZMod N, (e (x + y) : SchemeHomOver t f) = L.mul t (e x) (e y) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_zmod_prod_equiv_of_natCard_nsmul_eq_one_eq_sq.solution
