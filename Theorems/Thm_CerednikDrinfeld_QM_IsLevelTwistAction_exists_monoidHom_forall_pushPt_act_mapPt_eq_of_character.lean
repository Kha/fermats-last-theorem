import Definitions.Def_CerednikDrinfeld_QMFineModuli
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_IsLevelTwistAction_exists_monoidHom_forall_pushPt_act_mapPt_eq_of_character

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.IsLevelTwistAction.exists_monoidHom_forall_pushPt_act_mapPt_eq_of_character
    {a b a₁ b₁ : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsOrder Λ) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (N n : ℕ) [NeZero n]
    {𝒪 : Type} [CommRing 𝒪] {M : Scheme.{0}} {fM : M ⟶ Spec (CommRingCat.of 𝒪)}
    {ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N n S → SchemeHomOver s fM}
    {G : Type} [Group G] {ρ : G →* Aut M} {χ : G → ↥Λ} (hρ : IsLevelTwistAction Λ N n M fM ptF G ρ χ)
    {S : Type} [CommRing S] (A : FakeEllipticCurve Λ N S) (P : A.FullLevel n)
    (Γt : Subgroup (ℍ[ℚ, a₁, b₁])ˣ) (e : ↥Γt → (A.A ⟶ A.A)) (he : ∀ γ, e γ ≫ A.f = A.f)
    (hlab : ∃ lab : ↥Γt → ↥Λ,
        (∀ γ : ↥Γt, mapPt (e γ) (he γ) P.P = pushPt (A.act (lab γ)) (A.act_over (lab γ)) P.P) ∧
        (∀ γ γ' : ↥Γt, ∃ y : ↥Λ, (lab (γ * γ') : ℍ[ℚ, a, b]) - (lab γ' : ℍ[ℚ, a, b]) * (lab γ : ℍ[ℚ, a, b]) = (n : ℚ) • (y : ℍ[ℚ, a, b])) ∧
        (∀ (γ : ↥Γt) (c : ℤ), ((γ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) = (c : ℚ) • (1 : ℍ[ℚ, a₁, b₁]) →
            ∃ y : ↥Λ, (lab γ : ℍ[ℚ, a, b]) - (c : ℚ) • (1 : ℍ[ℚ, a, b]) = (n : ℚ) • (y : ℍ[ℚ, a, b])))
    (κ : ↥Γt →* (ZMod n)ˣ) :
    ∃ θt : ↥Γt →* G,
      ∀ γ : ↥Γt, pushPt (A.act (χ (θt γ))) (A.act_over (χ (θt γ))) (mapPt (e γ) (he γ) P.P) =
        pushPt (A.act ⟨((((κ γ : (ZMod n)ˣ) : ZMod n).val : ℤ) : ℚ), hΛℤ _⟩) (A.act_over _) P.P := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_IsLevelTwistAction_exists_monoidHom_forall_pushPt_act_mapPt_eq_of_character.solution
