import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_CerednikDrinfeld_QMIsogeny
import Definitions.Def_AlgebraicGeometry_FormalGroupAlongSection
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_CerednikDrinfeld_QMFormalCompletionAlong
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_le_isOrder_forall_exists_pow_smul_mem_and_act_and_forall_exists_generalLinearGroup_and_exists_isMaximalOrder_inf_eq_of_isOrder_act_of_conj_of_injective
attribute [-instance] MvFormalGroup.Points.instNeg MvFormalGroup.Points.instZero MvFormalGroup.Points.instAdd MvFormalGroup.Points.instAddCommGroup MvFormalGroup.Points.instAddGroup
attribute [-simp] MvFormalGroup.Points.mk.injEq MvFormalGroup.Points.mk.sizeOf_spec

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld
  CerednikDrinfeld.SpecialFormal CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve
open scoped Quaternion MatrixGroups

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_le_isOrder_forall_exists_pow_smul_mem_and_act_and_forall_exists_generalLinearGroup_and_exists_isMaximalOrder_inf_eq_of_isOrder_act_of_conj_of_injective
    {r : ℕ} [Fact r.Prime]

    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (coord : ↥Λ → Zp2 r × Zp2 r) (hcoord : IsOrderCoord Λ r coord) {N : ℕ}

    {B : Type} [CommRing B] (hq : IsNilpotent (r : B))

    (A₀ : FakeEllipticCurve Λ N B) (X₀ : FormalODModule r B) (θ₀ : RelativeGroupLaw.FormalCoordinates A₀.f 2)
    (hθ₀ : A₀.IsFormalModuleVia coord X₀ θ₀)

    {a₁ b₁ : ℚ} (ha₁ : a₁ ≠ 0) (hb₁ : b₁ ≠ 0) (R : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hR : IsOrder R)
    (ε : ↥R → (A₀.A ⟶ A₀.A)) (hε : ∀ x : ↥R, ε x ≫ A₀.f = A₀.f)
    (hε_hom : ∀ (x : ↥R) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P Q : SchemeHomOver t A₀.f),
      pushPt (ε x) (hε x) (A₀.L.mul t P Q) = A₀.L.mul t (pushPt (ε x) (hε x) P) (pushPt (ε x) (hε x) Q))
    (hε_lin : ∀ (x : ↥R) (m : ↥Λ), A₀.act m ≫ ε x = ε x ≫ A₀.act m)
    (hε_one : ∀ h : (1 : ℍ[ℚ, a₁, b₁]) ∈ R, ε ⟨1, h⟩ = 𝟙 A₀.A)
    (hε_mul : ∀ (x y : ↥R) (h : (x : ℍ[ℚ, a₁, b₁]) * (y : ℍ[ℚ, a₁, b₁]) ∈ R),
      ε ⟨(x : ℍ[ℚ, a₁, b₁]) * (y : ℍ[ℚ, a₁, b₁]), h⟩ = ε y ≫ ε x)
    (hε_add : ∀ (x y : ↥R) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P : SchemeHomOver t A₀.f),
      pushPt (ε (x + y)) (hε (x + y)) P = A₀.L.mul t (pushPt (ε x) (hε x) P) (pushPt (ε y) (hε y) P))

    (Γt : Subgroup (ℍ[ℚ, a₁, b₁])ˣ) (u : (ℍ[ℚ, a₁, b₁])ˣ)
    (e : ↥Γt → (A₀.A ⟶ A₀.A)) (he : ∀ γ, e γ ≫ A₀.f = A₀.f)
    (K : ↥Γt → ℕ) (x : ↥Γt → ↥R)
    (hx : ∀ γ : ↥Γt, (x γ : ℍ[ℚ, a₁, b₁]) =
      ((r ^ K γ : ℕ) : ℚ) • ((u⁻¹ * (γ : (ℍ[ℚ, a₁, b₁])ˣ) * u : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]))
    (he_eq : ∀ γ : ↥Γt, e γ = ε (x γ))

    (R₁ : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hR₁ : IsOrder R₁) (R' : Submodule ℤ ℍ[ℚ, a₁, b₁])
    (hR₁R' : ∀ z : ↥R₁, ∃ K : ℕ,
      ((r ^ K : ℕ) : ℚ) • (((u⁻¹ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) * (z : ℍ[ℚ, a₁, b₁]) * ((u : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁])) ∈ R')
    (hR'R : ∀ y : ↥R', ∃ (K : ℕ) (hK : ((r ^ K : ℕ) : ℚ) • (y : ℍ[ℚ, a₁, b₁]) ∈ R),
      FakeEllipticCurve.PreservesLevel A₀ A₀ (ε ⟨((r ^ K : ℕ) : ℚ) • (y : ℍ[ℚ, a₁, b₁]), hK⟩) (hε _))

    (hε_inj : ∀ z y : ↥R, ε z = ε y → z = y)
    (hε_surj : ∀ (φ : A₀.A ⟶ A₀.A) (hφ : φ ≫ A₀.f = A₀.f),
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P Q : SchemeHomOver t A₀.f),
        mapPt φ hφ (A₀.L.mul t P Q) = A₀.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q)) →
      (∀ m : ↥Λ, A₀.act m ≫ φ = φ ≫ A₀.act m) → ∃ z : ↥R, φ = ε z)
    (hdivq : ∀ (q : ℕ), q.Prime → q ≠ r → ∀ (φ : A₀.A ⟶ A₀.A) (hφ : φ ≫ A₀.f = A₀.f),
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P Q : SchemeHomOver t A₀.f),
        mapPt φ hφ (A₀.L.mul t P Q) = A₀.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q)) →
      (∀ m : ↥Λ, A₀.act m ≫ φ = φ ≫ A₀.act m) →
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P : SchemeHomOver t A₀.f),
        nsmulPt A₀.L t q P = A₀.L.one t → mapPt φ hφ P = A₀.L.one t) →
      ∃ (ψ : A₀.A ⟶ A₀.A) (hψ : ψ ≫ A₀.f = A₀.f),
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P Q : SchemeHomOver t A₀.f),
          mapPt ψ hψ (A₀.L.mul t P Q) = A₀.L.mul t (mapPt ψ hψ P) (mapPt ψ hψ Q)) ∧
        (∀ m : ↥Λ, A₀.act m ≫ ψ = ψ ≫ A₀.act m) ∧
        φ = A₀.act ⟨((q : ℤ) : ℚ), hΛℤ q⟩ ≫ ψ)
    (Λ₁ Λ₁s : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hΛ₁s : IsMaximalOrder Λ₁s) (hR₁Λ₁s : R₁ ≤ Λ₁s) (htwin : Λ₁ ⊓ Λ₁s = R₁)
    (hΛ₁sR : ∀ z : ↥Λ₁s, ∃ K : ℕ,
      ((r ^ K : ℕ) : ℚ) • (((u⁻¹ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) * (z : ℍ[ℚ, a₁, b₁]) * ((u : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁])) ∈ R)
    (hRΛ₁s : ∀ w : ↥R, ∃ K : ℕ,
      ((r ^ K : ℕ) : ℚ) • (((u : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) * (w : ℍ[ℚ, a₁, b₁]) * ((u⁻¹ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁])) ∈ Λ₁s)

    (K₀ : Type) [Field K₀] [CharZero K₀] (ι₀ : ℍ[ℚ, a₁, b₁] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) K₀) :
    ∃ (R₂ : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hR₂ : R₂ ≤ R₁) (hR₂o : IsOrder R₂)
      (hR₂r : ∀ z : ↥R₁, ∃ c : ℕ, ((r ^ c : ℕ) : ℚ) • (z : ℍ[ℚ, a₁, b₁]) ∈ R₂)
      (ê : ↥R₂ → (A₀.A ⟶ A₀.A)) (hê : ∀ z, ê z ≫ A₀.f = A₀.f),

      (∀ z : ↥R₂,
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P Q : SchemeHomOver t A₀.f),
            mapPt (ê z) (hê z) (A₀.L.mul t P Q) = A₀.L.mul t (mapPt (ê z) (hê z) P) (mapPt (ê z) (hê z) Q)) ∧
        (∀ m : ↥Λ, A₀.act m ≫ ê z = ê z ≫ A₀.act m) ∧
        FakeEllipticCurve.PreservesLevel A₀ A₀ (ê z) (hê z)) ∧

      (∀ h : (1 : ℍ[ℚ, a₁, b₁]) ∈ R₂, ê ⟨1, h⟩ = 𝟙 A₀.A) ∧
      (∀ (z y : ↥R₂) (h : (z : ℍ[ℚ, a₁, b₁]) * (y : ℍ[ℚ, a₁, b₁]) ∈ R₂),
          ê ⟨(z : ℍ[ℚ, a₁, b₁]) * (y : ℍ[ℚ, a₁, b₁]), h⟩ = ê y ≫ ê z) ∧
      (∀ (m : ℤ) (h : ((m : ℚ) : ℍ[ℚ, a₁, b₁]) ∈ R₂), ê ⟨((m : ℚ) : ℍ[ℚ, a₁, b₁]), h⟩ = A₀.act ⟨((m : ℤ) : ℚ), hΛℤ m⟩) ∧

      (∀ (z y : ↥R₂) (nx : ℤ), (y : ℍ[ℚ, a₁, b₁]) = star (z : ℍ[ℚ, a₁, b₁]) → nrd (z : ℍ[ℚ, a₁, b₁]) = (nx : ℚ) →
          ê y ≫ ê z = A₀.act ⟨((nx : ℤ) : ℚ), hΛℤ nx⟩) ∧

      (∀ (γ : ↥Γt) (z : ↥R₂) (k : ℕ),
          (z : ℍ[ℚ, a₁, b₁]) = ((r ^ k : ℕ) : ℚ) • ((γ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) →
          ∃ i j : ℕ, e γ ≫ A₀.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ê z ≫ A₀.act ⟨(((r ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩) ∧

      (∀ E₀ : ↥(Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd})) →+* Matrix (Fin 2) (Fin 2) K₀, Function.Injective E₀ →
        ∃ g : Matrix.GeneralLinearGroup (Fin 2) K₀,
          (∀ γ : ↥Γt, ∃ (εX : ↥(Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd}))) (kγ : ℤ),
            (∀ (B' : Type) [CommRing B'] [Algebra B B'] (J : Ideal B') (m : ℕ),
                J ^ (m + 1) = ⊥ → ∀ s : Fin 2 → B', (∀ i, s i ∈ J) →
                θ₀ B' (fun i => MvFormalGroup.nilEval m ((εX : MvFormalGroup.End X₀.F).toPowerSeries i) s) =
                  mapPt (e γ) (he γ) (θ₀ B' s)) ∧
            E₀ εX = ((r : K₀) ^ kγ) • ((g : Matrix (Fin 2) (Fin 2) K₀) * ι₀ ((γ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) *
              ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀))) ∧
          (∀ z : ↥R₂, ∃ (εX : ↥(Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd}))) (kx : ℤ),
            (∀ (B' : Type) [CommRing B'] [Algebra B B'] (J : Ideal B') (m : ℕ),
                J ^ (m + 1) = ⊥ → ∀ s : Fin 2 → B', (∀ i, s i ∈ J) →
                θ₀ B' (fun i => MvFormalGroup.nilEval m ((εX : MvFormalGroup.End X₀.F).toPowerSeries i) s) =
                  mapPt (ê z) (hê z) (θ₀ B' s)) ∧
            E₀ εX = ((r : K₀) ^ kx) • ((g : Matrix (Fin 2) (Fin 2) K₀) * ι₀ (z : ℍ[ℚ, a₁, b₁]) *
              ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀)))) ∧

      (∀ z : ↥R₂, star (z : ℍ[ℚ, a₁, b₁]) ∈ R₂) ∧

      (∃ (Λ₁s : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hΛ₁s : IsMaximalOrder Λ₁s) (hR₁Λ₁s : R₁ ≤ Λ₁s) (htwin : Λ₁ ⊓ Λ₁s = R₁)
          (R₂' : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hR₂' : R₂' ≤ Λ₁s) (hR₂'o : IsOrder R₂')
          (hR₂'r : ∀ z : ↥Λ₁s, ∃ c : ℕ, ((r ^ c : ℕ) : ℚ) • (z : ℍ[ℚ, a₁, b₁]) ∈ R₂') (hR₂R₂' : R₂ ≤ R₂')
          (ê' : ↥R₂' → (A₀.A ⟶ A₀.A)) (hê' : ∀ z, ê' z ≫ A₀.f = A₀.f),

        (∀ z : ↥R₂',
          (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P Q : SchemeHomOver t A₀.f),
              mapPt (ê' z) (hê' z) (A₀.L.mul t P Q) = A₀.L.mul t (mapPt (ê' z) (hê' z) P) (mapPt (ê' z) (hê' z) Q)) ∧
          (∀ m : ↥Λ, A₀.act m ≫ ê' z = ê' z ≫ A₀.act m)) ∧

        (∀ h : (1 : ℍ[ℚ, a₁, b₁]) ∈ R₂', ê' ⟨1, h⟩ = 𝟙 A₀.A) ∧
        (∀ (z y : ↥R₂') (h : (z : ℍ[ℚ, a₁, b₁]) * (y : ℍ[ℚ, a₁, b₁]) ∈ R₂'),
            ê' ⟨(z : ℍ[ℚ, a₁, b₁]) * (y : ℍ[ℚ, a₁, b₁]), h⟩ = ê' y ≫ ê' z) ∧
        (∀ (m : ℤ) (h : ((m : ℚ) : ℍ[ℚ, a₁, b₁]) ∈ R₂'), ê' ⟨((m : ℚ) : ℍ[ℚ, a₁, b₁]), h⟩ = A₀.act ⟨((m : ℤ) : ℚ), hΛℤ m⟩) ∧

        (∀ (z y : ↥R₂') (nz : ℤ), (y : ℍ[ℚ, a₁, b₁]) = star (z : ℍ[ℚ, a₁, b₁]) → nrd (z : ℍ[ℚ, a₁, b₁]) = (nz : ℚ) →
            ê' y ≫ ê' z = A₀.act ⟨((nz : ℤ) : ℚ), hΛℤ nz⟩) ∧

        (∀ z : ↥R₂, ê' ⟨(z : ℍ[ℚ, a₁, b₁]), hR₂R₂' z.2⟩ = ê z) ∧

        (∀ z : ↥R₂', star (z : ℍ[ℚ, a₁, b₁]) ∈ R₂') ∧
        (∀ z y : ↥R₂', ê' z = ê' y → z = y) ∧

        (∀ (q : ℕ), q.Prime → q ≠ r → ∀ z : ↥R₂',
          (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P : SchemeHomOver t A₀.f),
              nsmulPt A₀.L t q P = A₀.L.one t → mapPt (ê' z) (hê' z) P = A₀.L.one t) →
          ∃ (K : ℕ) (y : ↥Λ₁s), ((r ^ K : ℕ) : ℚ) • (z : ℍ[ℚ, a₁, b₁]) = (q : ℚ) • (y : ℍ[ℚ, a₁, b₁]))) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_le_isOrder_forall_exists_pow_smul_mem_and_act_and_forall_exists_generalLinearGroup_and_exists_isMaximalOrder_inf_eq_of_isOrder_act_of_conj_of_injective.solution
