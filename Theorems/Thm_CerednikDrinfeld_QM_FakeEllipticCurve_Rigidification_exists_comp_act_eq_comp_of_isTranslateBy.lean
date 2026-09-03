import Mathlib
import Definitions.Def_CerednikDrinfeld_QMRigidification
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_comp_act_eq_comp_of_isTranslateBy

set_option autoImplicit false

open Quaternion CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve

theorem CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_comp_act_eq_comp_of_isTranslateBy
    {r : ℕ} {𝒪 : Type} [CommRing 𝒪] {π : 𝒪} {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    {A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π})}
    {B : Type} [CommRing B] [Algebra 𝒪 B] {ψ : Onr →ₐ[𝒪] B} {E : FakeEllipticCurve Λ N B}
    (ρ ρ' : Rigidification r π A₀ ψ E) (f f' : A₀.A ⟶ A₀.A) (dγ : ℕ)
    (hff' : FakeEllipticCurve.IsIsogenyPair (r ^ dγ) A₀ A₀ f f') (htr : Rigidification.IsTranslateBy hΛℤ f ρ ρ') :
    ∃ (u : ρ'.Eb.A ⟶ ρ.Eb.A) (uA : ρ'.Ab.A ⟶ ρ.Ab.A) (_ : Rigidification.IsComparison ρ ρ' u uA)
      (f'b : ρ.Ab.A ⟶ ρ.Ab.A) (_ : f'b ≫ ρ.gA = ρ.gA ≫ f') (_ : f'b ≫ ρ.Ab.f = ρ.Ab.f) (i j : ℕ),
      ρ'.φ' ≫ u ≫ ρ.Eb.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩ =
        uA ≫ f'b ≫ ρ.φ' ≫ ρ.Eb.act ⟨(((r ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_comp_act_eq_comp_of_isTranslateBy.solution
