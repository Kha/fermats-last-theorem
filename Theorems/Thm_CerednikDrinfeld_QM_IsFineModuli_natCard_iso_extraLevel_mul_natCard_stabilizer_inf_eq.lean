import Definitions.Def_CerednikDrinfeld_QMFineModuli
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_IsFineModuli_natCard_iso_extraLevel_mul_natCard_stabilizer_inf_eq

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.IsFineModuli.natCard_iso_extraLevel_mul_natCard_stabilizer_inf_eq
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (N m : ℕ)
    {𝒪 : Type} [CommRing 𝒪] (hm' : IsUnit ((m : ℕ) : 𝒪))

    {M : Scheme.{0}} {πM : M ⟶ Spec (CommRingCat.of 𝒪)}
    {ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N m S → SchemeHomOver s πM}
    (hM : IsFineModuli Λ N m M πM ptF)
    {G : Type} [Group G] [Finite G] {ρ : G →* Aut M} {χ : G → ↥Λ}
    (hρ : IsLevelTwistAction Λ N m M πM ptF G ρ χ)

    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓm : ℓ ∣ m)
    (L₀ : Submodule ℤ ℍ[ℚ, a, b]) (hL₀ : L₀ ≤ Λ) (hℓL₀ : ∀ x : ↥Λ, (ℓ : ℚ) • (x : ℍ[ℚ, a, b]) ∈ L₀)
    (hL₀_left : ∀ (y : ↥Λ) (x : ℍ[ℚ, a, b]), x ∈ L₀ → (y : ℍ[ℚ, a, b]) * x ∈ L₀)
    (hL₀_index : L₀.toAddSubgroup.relIndex Λ.toAddSubgroup = ℓ ^ 2)
    (H : Subgroup G) (hH : ∀ g : G, g ∈ H ↔ ∀ x : ℍ[ℚ, a, b], x ∈ L₀ → x * (χ g : ℍ[ℚ, a, b]) ∈ L₀)

    (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of 𝒪))
    (u : FakeEllipticCurve.WithFullLevel Λ N m k)
    (n : ℕ) (K : Fin n → u.1.ExtraLevel ℓ)
    (hKdist : ∀ i j : Fin n,
      (∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) u.1.f,
        FactorsThrough (K i).levK x ↔ FactorsThrough (K j).levK x) → i = j)
    (hKexh : ∀ K' : u.1.ExtraLevel ℓ, ∃ i : Fin n,
      ∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) u.1.f,
        FactorsThrough K'.levK x ↔ FactorsThrough (K i).levK x)

    (i₀ : Fin n)
    (hK₀ : ∀ (k' : Type) [Field k'] [IsAlgClosed k'] (sk : k →+* k') (Q : SchemeHomOver (geomPoint k' sk) u.1.f),
      FactorsThrough (K i₀).levK Q ↔
        ∃ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ ∧
          pushPt (u.1.act x) (u.1.act_over x)
            (nsmulPt u.1.L (geomPoint k' sk) (m / ℓ) (FakeEllipticCurve.sectionAt u.2.P k' sk)) = Q) :
    Nat.card {i : Fin n // FakeEllipticCurve.WithExtraLevel.Iso
        (⟨u.1, K i⟩ : FakeEllipticCurve.WithExtraLevel Λ N ℓ k) ⟨u.1, K i₀⟩} *
      Nat.card {g : G // g ∈ H ∧ (ptF k s u).1 ≫ (ρ g).hom = (ptF k s u).1} =
    Nat.card {g : G // (ptF k s u).1 ≫ (ρ g).hom = (ptF k s u).1} := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_IsFineModuli_natCard_iso_extraLevel_mul_natCard_stabilizer_inf_eq.solution
