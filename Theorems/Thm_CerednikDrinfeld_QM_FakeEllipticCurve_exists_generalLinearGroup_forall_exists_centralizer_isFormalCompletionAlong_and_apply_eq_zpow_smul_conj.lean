import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_AlgebraicGeometry_FormalGroupAlongSection
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_CerednikDrinfeld_QMFormalCompletionAlong
import Definitions.Def_QuaternionAlgebra_Order
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_generalLinearGroup_forall_exists_centralizer_isFormalCompletionAlong_and_apply_eq_zpow_smul_conj
attribute [-instance] MvFormalGroup.Points.instNeg MvFormalGroup.Points.instZero MvFormalGroup.Points.instAdd MvFormalGroup.Points.instAddCommGroup MvFormalGroup.Points.instAddGroup
attribute [-simp] MvFormalGroup.Points.mk.injEq MvFormalGroup.Points.mk.sizeOf_spec

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld
  CerednikDrinfeld.SpecialFormal CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve
open scoped Quaternion MatrixGroups

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_generalLinearGroup_forall_exists_centralizer_isFormalCompletionAlong_and_apply_eq_zpow_smul_conj
    {q : ℕ} [Fact q.Prime]

    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (coord : ↥Λ → Zp2 q × Zp2 q) (hcoord : IsOrderCoord Λ q coord) {N : ℕ}

    {B : Type} [CommRing B] (hq : IsNilpotent (q : B))

    (A₀ : FakeEllipticCurve Λ N B) (X₀ : FormalODModule q B) (θ₀ : RelativeGroupLaw.FormalCoordinates A₀.f 2)
    (hθ₀ : A₀.IsFormalModuleVia coord X₀ θ₀)

    {a₁ b₁ : ℚ} (ha₁ : a₁ ≠ 0) (hb₁ : b₁ ≠ 0) (R₁ : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hR₁ : IsOrder R₁)
    (c₀ : ℕ) (e : ↥R₁ → (A₀.A ⟶ A₀.A)) (he : ∀ x : ↥R₁, e x ≫ A₀.f = A₀.f)
    (hhom : ∀ (x : ↥R₁) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P Q : SchemeHomOver t A₀.f),
      pushPt (e x) (he x) (A₀.L.mul t P Q) = A₀.L.mul t (pushPt (e x) (he x) P) (pushPt (e x) (he x) Q))
    (hlin : ∀ (x : ↥R₁) (m : ↥Λ), A₀.act m ≫ e x = e x ≫ A₀.act m)
    (hadd : ∀ (x y : ↥R₁) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P : SchemeHomOver t A₀.f),
      pushPt (e (x + y)) (he (x + y)) P = A₀.L.mul t (pushPt (e x) (he x) P) (pushPt (e y) (he y) P))
    (hmul : ∀ (x y : ↥R₁) (hxy : (x : ℍ[ℚ, a₁, b₁]) * (y : ℍ[ℚ, a₁, b₁]) ∈ R₁)
      {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P : SchemeHomOver t A₀.f),
      nsmulPt A₀.L t (q ^ c₀) (pushPt (e ⟨(x : ℍ[ℚ, a₁, b₁]) * (y : ℍ[ℚ, a₁, b₁]), hxy⟩) (he _) P) =
        pushPt (e x) (he x) (pushPt (e y) (he y) P))
    (hone : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P : SchemeHomOver t A₀.f),
      pushPt (e ⟨1, hR₁.one_mem⟩) (he _) P = nsmulPt A₀.L t (q ^ c₀) P)

    {I : Type} (w : I → ℍ[ℚ, a₁, b₁]) (eI : I → (A₀.A ⟶ A₀.A)) (heI : ∀ i : I, eI i ≫ A₀.f = A₀.f)
    (heIhom : ∀ (i : I) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P Q : SchemeHomOver t A₀.f),
      pushPt (eI i) (heI i) (A₀.L.mul t P Q) = A₀.L.mul t (pushPt (eI i) (heI i) P) (pushPt (eI i) (heI i) Q))
    (heIlin : ∀ (i : I) (m : ↥Λ), A₀.act m ≫ eI i = eI i ≫ A₀.act m)
    (hI : ∀ i : I, ∃ (k j : ℕ) (x : ↥R₁), (x : ℍ[ℚ, a₁, b₁]) = ((q ^ k : ℕ) : ℚ) • w i ∧
      eI i ≫ A₀.act ⟨(((q ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = e x)

    (K₀ : Type) [Field K₀] [CharZero K₀] (ι₀ : ℍ[ℚ, a₁, b₁] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) K₀)
    (𝓔 : Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd}) →+* Matrix (Fin 2) (Fin 2) K₀) :
    ∃ g : GL (Fin 2) K₀, ∀ i : I,
      ∃ (ε : ↥(Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd}))) (ki : ℤ),
        IsFormalCompletionAlong θ₀ θ₀ (eI i) (heI i) (MvFormalGroup.Hom.toPowerSeries (ε : MvFormalGroup.End X₀.F)) ∧
        𝓔 ε = ((q : K₀) ^ ki) • ((g : Matrix (Fin 2) (Fin 2) K₀) * ι₀ (w i) *
          ((g⁻¹ : GL (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀)) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_generalLinearGroup_forall_exists_centralizer_isFormalCompletionAlong_and_apply_eq_zpow_smul_conj.solution
