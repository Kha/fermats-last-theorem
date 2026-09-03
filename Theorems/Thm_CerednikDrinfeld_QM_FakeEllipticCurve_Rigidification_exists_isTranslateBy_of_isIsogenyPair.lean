import Definitions.Def_CerednikDrinfeld_QMRigidification
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_isTranslateBy_of_isIsogenyPair

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry NeronModelInfra CerednikDrinfeld CerednikDrinfeld.QM

theorem CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_isTranslateBy_of_isIsogenyPair
    {r : ℕ} [Fact r.Prime] {𝒪 : Type} [CommRing 𝒪] {π : 𝒪} {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    {A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π})}
    (eγ eγ' : A₀.A ⟶ A₀.A) (heγ : eγ ≫ A₀.f = A₀.f) (dγ : ℕ)
    (hpair : FakeEllipticCurve.IsIsogenyPair (r ^ dγ) A₀ A₀ eγ eγ')
    (hlev : FakeEllipticCurve.PreservesLevel A₀ A₀ eγ heγ)
    {B : Type} [CommRing B] [Algebra 𝒪 B] {ψ : Onr →ₐ[𝒪] B} {E : FakeEllipticCurve Λ N B}
    (ϱ : FakeEllipticCurve.Rigidification r π A₀ ψ E) :
    ∃ ρ₂ : FakeEllipticCurve.Rigidification r π A₀ ψ E,
      FakeEllipticCurve.Rigidification.IsTranslateBy hΛℤ eγ ϱ ρ₂ ∧
      (∀ (ℓ : ℕ) (K₀ : A₀.ExtraLevel ℓ),
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))) (R : SchemeHomOver t A₀.f),
            FactorsThrough K₀.levK R → FactorsThrough K₀.levK (mapPt eγ heγ R)) →
        ∀ (C : E.ExtraLevel ℓ),
          (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (B ⧸ Ideal.span {algebraMap 𝒪 B π}))) (R : SchemeHomOver t' ϱ.Eb.f),
              (∃ R₀ : T ⟶ C.K, R₀ ≫ C.levK = R.1 ≫ ϱ.gb) → ∃ Q₀ : T ⟶ K₀.K, Q₀ ≫ K₀.levK = (R.1 ≫ ϱ.φ) ≫ ϱ.gA) →
          (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (B ⧸ Ideal.span {algebraMap 𝒪 B π}))) (R : SchemeHomOver t' ρ₂.Eb.f),
              (∃ R₀ : T ⟶ C.K, R₀ ≫ C.levK = R.1 ≫ ρ₂.gb) → ∃ Q₀ : T ⟶ K₀.K, Q₀ ≫ K₀.levK = (R.1 ≫ ρ₂.φ) ≫ ρ₂.gA)) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_isTranslateBy_of_isIsogenyPair.solution
