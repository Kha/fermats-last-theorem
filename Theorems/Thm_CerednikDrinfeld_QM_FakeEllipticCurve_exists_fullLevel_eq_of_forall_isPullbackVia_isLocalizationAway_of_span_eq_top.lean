import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fullLevel_eq_of_forall_isPullbackVia_isLocalizationAway_of_span_eq_top

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_fullLevel_eq_of_forall_isPullbackVia_isLocalizationAway_of_span_eq_top
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    {S : Type} [CommRing S] (E : FakeEllipticCurve Λ N S) (m : ℕ)
    (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) E.f)
    (n : ℕ) (c : Fin n → S) (hc : Ideal.span (Set.range c) = ⊤)
    (L : Fin n → Type) [∀ i, CommRing (L i)] [∀ i, Algebra S (L i)] [∀ i, IsLocalization.Away (c i) (L i)]
    (Ei : ∀ i, FakeEllipticCurve Λ N (L i)) (g : ∀ i, (Ei i).A ⟶ E.A)
    (hg : ∀ i, FakeEllipticCurve.IsPullbackVia (algebraMap S (L i)) E (Ei i) (g i))
    (Pi : ∀ i, (Ei i).FullLevel m)
    (hPi : ∀ i, ((Pi i).P).1 ≫ g i = Spec.map (CommRingCat.ofHom (algebraMap S (L i))) ≫ P.1) :
    ∃ Pm : E.FullLevel m, Pm.P = P := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fullLevel_eq_of_forall_isPullbackVia_isLocalizationAway_of_span_eq_top.solution
