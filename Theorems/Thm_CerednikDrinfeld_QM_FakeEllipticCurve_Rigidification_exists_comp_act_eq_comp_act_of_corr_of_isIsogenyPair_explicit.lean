import Mathlib
import Definitions.Def_CerednikDrinfeld_QMRigidification
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_comp_act_eq_comp_act_of_corr_of_isIsogenyPair_explicit

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_comp_act_eq_comp_act_of_corr_of_isIsogenyPair_explicit
    {r : ℕ} {𝒪 : Type} [CommRing 𝒪] {π : 𝒪} {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    {A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π})}
    {B : Type} [CommRing B] [Algebra 𝒪 B] {ψ : Onr →ₐ[𝒪] B} {E Ef : FakeEllipticCurve Λ N B}
    (ρ : FakeEllipticCurve.Rigidification r π A₀ ψ E) (ρf : FakeEllipticCurve.Rigidification r π A₀ ψ Ef)

    (q : E.A ⟶ Ef.A) (q' : Ef.A ⟶ E.A) (Dq : ℕ) (hqq' : FakeEllipticCurve.IsIsogenyPair Dq E Ef q q')
    (f f' : A₀.A ⟶ A₀.A) (D : ℕ) (hff' : FakeEllipticCurve.IsIsogenyPair D A₀ A₀ f f')

    (qb : ρ.Eb.A ⟶ ρf.Eb.A) (hqb : qb ≫ ρf.gb = ρ.gb ≫ q) (hqbf : qb ≫ ρf.Eb.f = ρ.Eb.f)
    (uA : ρf.Ab.A ⟶ ρ.Ab.A) (huA : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρ.Ab ρf.Ab uA) (huAg : uA ≫ ρ.gA = ρf.gA)
    (eb : ρ.Ab.A ⟶ ρ.Ab.A) (heb : eb ≫ ρ.gA = ρ.gA ≫ f) (hebf : eb ≫ ρ.Ab.f = ρ.Ab.f)
    (i j : ℕ)
    (hP : qb ≫ ρf.φ ≫ uA ≫ ρ.Ab.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ρ.φ ≫ eb ≫ ρ.Ab.act ⟨(((r ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩) :
    ∃ (f'b : ρ.Ab.A ⟶ ρ.Ab.A) (_ : f'b ≫ ρ.gA = ρ.gA ≫ f') (_ : f'b ≫ ρ.Ab.f = ρ.Ab.f),
      uA ≫ f'b ≫ ρ.φ' ≫ qb ≫ ρf.Eb.act ⟨(((Dq * r ^ (i + ρf.d) : ℕ) : ℤ) : ℚ), hΛℤ _⟩ =
        ρf.φ' ≫ ρf.Eb.act ⟨(((Dq * D * r ^ (j + ρ.d) : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_comp_act_eq_comp_act_of_corr_of_isIsogenyPair_explicit.solution
