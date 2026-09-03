import Definitions.Def_CerednikDrinfeld_QMFineModuli
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_IsFineModuli_exists_isFineModuli_of_isPullback

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra CerednikDrinfeld.QM

theorem CerednikDrinfeld.QM.IsFineModuli.exists_isFineModuli_of_isPullback
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N m : ℕ} {B B' : Type} [CommRing B] [CommRing B'] (β : B →+* B')
    {M : Scheme.{0}} {πM : M ⟶ Spec (CommRingCat.of B)}
    {ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)),
      FakeEllipticCurve.WithFullLevel Λ N m S → SchemeHomOver s πM}
    (hM : IsFineModuli Λ N m M πM ptF)
    {M' : Scheme.{0}} (πM' : M' ⟶ Spec (CommRingCat.of B')) (pr : M' ⟶ M)
    (hpr : CategoryTheory.IsPullback pr πM' πM (Spec.map (CommRingCat.ofHom β))) :
    ∃ ptF' : (∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B')),
        FakeEllipticCurve.WithFullLevel Λ N m S → SchemeHomOver s πM'),
      IsFineModuli Λ N m M' πM' ptF' ∧
      ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B'))
        (u : FakeEllipticCurve.WithFullLevel Λ N m S),
        (ptF' S s u).1 ≫ pr = (ptF S (s ≫ Spec.map (CommRingCat.ofHom β)) u).1 := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_IsFineModuli_exists_isFineModuli_of_isPullback.solution
