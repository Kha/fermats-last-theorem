import Definitions.Def_CerednikDrinfeld_FakeEllipticFrobenius
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_kernel_of_isFinite_of_flat

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_kernel_of_isFinite_of_flat
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    {S : Type u} [CommRing S] (𝒜 𝒟 : FakeEllipticCurve Λ N S)
    (Φ : 𝒜.A ⟶ 𝒟.A) (hΦ : Φ ≫ 𝒟.f = 𝒜.f) [IsFinite Φ] [Flat Φ] [LocallyOfFinitePresentation Φ] :
    ∃ (Kk : Scheme.{u}) (ι : Kk ⟶ 𝒜.A),
      IsClosedImmersion ι ∧ IsFinite (ι ≫ 𝒜.f) ∧ Flat (ι ≫ 𝒜.f) ∧ LocallyOfFinitePresentation (ι ≫ 𝒜.f) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t 𝒜.f),
        FactorsThrough ι P ↔ mapPt Φ hΦ P = 𝒟.L.one t) ∧
      (∀ s : ↥(Spec (CommRingCat.of S)),
        (ι ≫ 𝒜.f).finrank s = Φ.finrank ((𝒟.L.one (𝟙 (Spec (CommRingCat.of S)))).1.base s)) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_kernel_of_isFinite_of_flat.solution
