import Definitions.Def_CerednikDrinfeld_QMRigidification
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_isoVia_corr_of_isPullbackVia

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian

theorem CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_isoVia_corr_of_isPullbackVia
    {r N : ℕ}
    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪)
    (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr]
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (B B' : Type) [CommRing B] [Algebra 𝒪 B] [CommRing B'] [Algebra 𝒪 B'] (φ : B →ₐ[𝒪] B') (ψ : Onr →ₐ[𝒪] B)

    (E E' : FakeEllipticCurve Λ N B) (i : E.A ≅ E'.A) (hi : i.hom ≫ E'.f = E.f) (hiso : FakeEllipticCurve.IsoVia E E' i hi)
    (ϱ : FakeEllipticCurve.Rigidification r π A₀ ψ E) (ϱ' : FakeEllipticCurve.Rigidification r π A₀ ψ E')
    (ib : ϱ.Eb.A ⟶ ϱ'.Eb.A) (hibg : ib ≫ ϱ'.gb = ϱ.gb ≫ i.hom) (hibf : ib ≫ ϱ'.Eb.f = ϱ.Eb.f)
    (uA : ϱ'.Ab.A ⟶ ϱ.Ab.A) (huA : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ϱ.Ab ϱ'.Ab uA) (huAg : uA ≫ ϱ.gA = ϱ'.gA)
    (i₁ j₁ : ℕ)
    (hcorr : ib ≫ ϱ'.φ ≫ uA ≫ ϱ.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ϱ.φ ≫ ϱ.Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩)

    (Eφ : FakeEllipticCurve Λ N B') (g : Eφ.A ⟶ E.A) (hg : FakeEllipticCurve.IsPullbackVia (φ : B →+* B') E Eφ g)
    (E'φ : FakeEllipticCurve Λ N B') (g' : E'φ.A ⟶ E'.A) (hg' : FakeEllipticCurve.IsPullbackVia (φ : B →+* B') E' E'φ g')
    (ϱφ : FakeEllipticCurve.Rigidification r π A₀ (φ.comp ψ) Eφ) (hϱφ : FakeEllipticCurve.Rigidification.IsPullbackVia φ g hg ϱ ϱφ)
    (ϱ'φ : FakeEllipticCurve.Rigidification r π A₀ (φ.comp ψ) E'φ) (hϱ'φ : FakeEllipticCurve.Rigidification.IsPullbackVia φ g' hg' ϱ' ϱ'φ) :
    ∃ (iφ : Eφ.A ≅ E'φ.A) (hiφ : iφ.hom ≫ E'φ.f = Eφ.f) (_ : FakeEllipticCurve.IsoVia Eφ E'φ iφ hiφ)
      (_ : iφ.hom ≫ g' = g ≫ i.hom)
      (ibφ : ϱφ.Eb.A ⟶ ϱ'φ.Eb.A) (_ : ibφ ≫ ϱ'φ.gb = ϱφ.gb ≫ iφ.hom) (_ : ibφ ≫ ϱ'φ.Eb.f = ϱφ.Eb.f)
      (uAφ : ϱ'φ.Ab.A ⟶ ϱφ.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ϱφ.Ab ϱ'φ.Ab uAφ) (_ : uAφ ≫ ϱφ.gA = ϱ'φ.gA),
      ibφ ≫ ϱ'φ.φ ≫ uAφ ≫ ϱφ.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ϱφ.φ ≫ ϱφ.Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_isoVia_corr_of_isPullbackVia.solution
