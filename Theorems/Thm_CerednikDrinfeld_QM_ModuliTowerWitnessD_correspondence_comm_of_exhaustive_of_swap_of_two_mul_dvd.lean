import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Definitions.Def_CerednikDrinfeld_HeckeTower
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_CerednikDrinfeld_QMModuliTower
import Definitions.Def_CerednikDrinfeld_QMModuliTowerD
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_ModuliTowerWitnessD_correspondence_comm_of_exhaustive_of_swap_of_two_mul_dvd

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain AlgebraicCurve QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion TensorProduct NumberField

theorem CerednikDrinfeld.QM.ModuliTowerWitnessD.correspondence_comm_of_exhaustive_of_swap_of_two_mul_dvd
    {N q q' : ℕ} [NeZero N] [Fact q.Prime] [Fact q'.Prime] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q)
    (D : ℕ) (hD : 2 * N * q * q' ∣ D)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)

    (X : Scheme.{0}) [hXint : IsIntegral X]
    (πX : X ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ))))
    (pt : ∀ (S : Type) [CommRing S]
      (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ)))),
      FakeEllipticCurve Λ N S → SchemeHomOver s πX)
    (hsmooth : Smooth πX) (hproper : IsProper πX)
    (pt_iso : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ _) (E E' : FakeEllipticCurve Λ N S),
      FakeEllipticCurve.Iso E E' → pt S s E = pt S s E')
    (pt_pullback : ∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
      (s : Spec (CommRingCat.of S) ⟶ _) (s' : Spec (CommRingCat.of S') ⟶ _),
      Spec.map (CommRingCat.ofHom φ) ≫ s = s' → ∀ (E : FakeEllipticCurve Λ N S) (E' : FakeEllipticCurve Λ N S'),
      FakeEllipticCurve.IsPullback φ E E' → (pt S' s' E').1 = Spec.map (CommRingCat.ofHom φ) ≫ (pt S s E).1)
    (pt_surjective : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ _) (P : SchemeHomOver s πX),
      ∃ E : FakeEllipticCurve Λ N k, pt k s E = P)
    (pt_injective : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ _)
      (E E' : FakeEllipticCurve Λ N k), pt k s E = pt k s E' → FakeEllipticCurve.Iso E E')
    (hsmooth1 : SmoothOfRelativeDimension 1 πX)
    (hgeom : ∀ (k : Type) [Field k] [IsAlgClosed k]
      (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ)))),
      IsIntegral (CategoryTheory.Limits.pullback πX s))
    (sbar : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ))))
    (sbar_over : sbar ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ (Localization.Away ((D : ℕ) : ℤ)))) =
      Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))))

    (Fbar : Type) [Field Fbar] [Algebra (AlgebraicClosure ℚ) Fbar]
    [IsCurveOver (AlgebraicClosure ℚ) Fbar] [Algebra.EssFiniteType (AlgebraicClosure ℚ) Fbar]
    (gal : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* SemilinearAut (AlgebraicClosure ℚ) Fbar)
    (𝔐 : AlgebraicCurve.CurveModel (AlgebraicClosure ℚ) Fbar)
    (e𝔐 : 𝔐.C ⟶ CategoryTheory.Limits.pullback πX sbar) (he𝔐 : IsIso e𝔐)
    (he𝔐_snd : e𝔐 ≫ CategoryTheory.Limits.pullback.snd πX sbar = 𝔐.toBase)

    (𝕋 : HeckeTower.TowerData q q' Fbar)
    (galT : ∀ ℓ : HeckeTower.AwayPrime q q', (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* SemilinearAut (AlgebraicClosure ℚ) (𝕋.F ℓ))
    (W : Fin 2 → SemilinearAut (AlgebraicClosure ℚ) Fbar) (WT : ∀ ℓ : HeckeTower.AwayPrime q q', Fin 2 → SemilinearAut (AlgebraicClosure ℚ) (𝕋.F ℓ))
    (tw : ModuliTowerWitnessD Λ N q q' D Fbar X πX sbar pt 𝔐 e𝔐 gal 𝕋 galT W WT)

    (hEXH : ∀ (ℓ : HeckeTower.AwayPrime q q') (P : Place (AlgebraicClosure ℚ) Fbar) (E : FakeEllipticCurve Λ N (AlgebraicClosure ℚ)),
      (pt _ sbar E).1 = (𝔐.pointEquivPlace.symm P).1 ≫ e𝔐 ≫ CategoryTheory.Limits.pullback.fst πX sbar →
      ∃ (n : ℕ) (K : Fin n → E.ExtraLevel (ℓ.1 : ℕ)) (Q : Fin n → Place (AlgebraicClosure ℚ) Fbar),
        (∀ i j : Fin n,
            (∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) E.f, FactorsThrough (K i).levK x ↔ FactorsThrough (K j).levK x) → i = j) ∧
        (∀ K' : E.ExtraLevel (ℓ.1 : ℕ), ∃ i : Fin n,
            ∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) E.f, FactorsThrough K'.levK x ↔ FactorsThrough (K i).levK x) ∧
        (∀ i : Fin n,
            FakeEllipticCurve.IsLevelIsogeny (ℓ.1 : ℕ)
              (⟨E, K i⟩ : FakeEllipticCurve.WithExtraLevel Λ N (ℓ.1 : ℕ) (AlgebraicClosure ℚ)) (tw.rep (Q i))) ∧
        Divisor.correspondence (𝕋.φ (ℓ, 0)) (𝕋.φ (ℓ, 1)) (𝕋.integral (ℓ, 0)) (𝕋.integral (ℓ, 1)) (Finsupp.single P 1) =
          Finset.univ.sum (fun i : Fin n => Finsupp.single (Q i) 1))

    (hSWAP₁ : ∀ (ℓ ℓ' : ℕ) [Fact ℓ.Prime] [Fact ℓ'.Prime], ℓ ≠ ℓ' →
      ∀ (E E₁ : FakeEllipticCurve Λ N (AlgebraicClosure ℚ)) (K : E.ExtraLevel ℓ)
        (φ : E.A ⟶ E₁.A) (hφ : φ ≫ E₁.f = E.f) (ψ : E₁.A ⟶ E.A) (hψ : ψ ≫ E.f = E₁.f),
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P Q : SchemeHomOver t E.f),
          mapPt φ hφ (E.L.mul t P Q) = E₁.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q)) →
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P Q : SchemeHomOver t E₁.f),
          mapPt ψ hψ (E₁.L.mul t P Q) = E.L.mul t (mapPt ψ hψ P) (mapPt ψ hψ Q)) →
        (∀ x : ↥Λ, E.act x ≫ φ = φ ≫ E₁.act x) → (∀ x : ↥Λ, E₁.act x ≫ ψ = ψ ≫ E.act x) →
        (∀ hℓ : ((ℓ : ℚ) : ℍ[ℚ, a, b]) ∈ Λ,
          φ ≫ ψ = E.act ⟨((ℓ : ℚ) : ℍ[ℚ, a, b]), hℓ⟩ ∧ ψ ≫ φ = E₁.act ⟨((ℓ : ℚ) : ℍ[ℚ, a, b]), hℓ⟩) →
        (1 : ℍ[ℚ, a, b]) ∈ Λ →
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t E.f),
          mapPt φ hφ P = E₁.L.one t ↔ FactorsThrough K.levK P) →
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t E.f),
          FactorsThrough E.lev P → FactorsThrough E₁.lev (mapPt φ hφ P)) →
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (x : SchemeHomOver t E₁.f),
          FactorsThrough E₁.lev x → ∃ P : SchemeHomOver t E.f, FactorsThrough E.lev P ∧ mapPt φ hφ P = x) →
        (∀ K' : E.ExtraLevel ℓ', ∃ K₁' : E₁.ExtraLevel ℓ',
          ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (x : SchemeHomOver t E₁.f),
            FactorsThrough K₁'.levK x ↔ ∃ y : SchemeHomOver t E.f, FactorsThrough K'.levK y ∧ mapPt φ hφ y = x) ∧
        (∀ K₁' : E₁.ExtraLevel ℓ', ∃ K' : E.ExtraLevel ℓ',
          ∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) E₁.f,
            FactorsThrough K₁'.levK x ↔ ∃ y : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) E.f, FactorsThrough K'.levK y ∧ mapPt φ hφ y = x) ∧
        (∀ K' K'' : E.ExtraLevel ℓ',
          (∀ y : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) E.f, FactorsThrough K'.levK y ↔ FactorsThrough K''.levK y) ↔
          (∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) E₁.f,
              (∃ y : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) E.f, FactorsThrough K'.levK y ∧ mapPt φ hφ y = x) ↔
              (∃ y : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) E.f, FactorsThrough K''.levK y ∧ mapPt φ hφ y = x))))

    (hSWAP₂ : ∀ (ℓ ℓ' : ℕ) [Fact ℓ.Prime] [Fact ℓ'.Prime], ℓ ≠ ℓ' →
      ∀ (E E₁ E₁' d d' : FakeEllipticCurve Λ N (AlgebraicClosure ℚ)) (K : E.ExtraLevel ℓ) (K' : E.ExtraLevel ℓ')
        (φ : E.A ⟶ E₁.A) (hφ : φ ≫ E₁.f = E.f) (ψ : E₁.A ⟶ E.A) (hψ : ψ ≫ E.f = E₁.f),
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P Q : SchemeHomOver t E.f),
          mapPt φ hφ (E.L.mul t P Q) = E₁.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q)) →
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P Q : SchemeHomOver t E₁.f),
          mapPt ψ hψ (E₁.L.mul t P Q) = E.L.mul t (mapPt ψ hψ P) (mapPt ψ hψ Q)) →
        (∀ x : ↥Λ, E.act x ≫ φ = φ ≫ E₁.act x) → (∀ x : ↥Λ, E₁.act x ≫ ψ = ψ ≫ E.act x) →
        (∀ hℓ : ((ℓ : ℚ) : ℍ[ℚ, a, b]) ∈ Λ,
          φ ≫ ψ = E.act ⟨((ℓ : ℚ) : ℍ[ℚ, a, b]), hℓ⟩ ∧ ψ ≫ φ = E₁.act ⟨((ℓ : ℚ) : ℍ[ℚ, a, b]), hℓ⟩) →
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t E.f),
          mapPt φ hφ P = E₁.L.one t ↔ FactorsThrough K.levK P) →
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t E.f),
          FactorsThrough E.lev P → FactorsThrough E₁.lev (mapPt φ hφ P)) →
      ∀ (φ' : E.A ⟶ E₁'.A) (hφ' : φ' ≫ E₁'.f = E.f) (ψ' : E₁'.A ⟶ E.A) (hψ' : ψ' ≫ E.f = E₁'.f),
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P Q : SchemeHomOver t E.f),
          mapPt φ' hφ' (E.L.mul t P Q) = E₁'.L.mul t (mapPt φ' hφ' P) (mapPt φ' hφ' Q)) →
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P Q : SchemeHomOver t E₁'.f),
          mapPt ψ' hψ' (E₁'.L.mul t P Q) = E.L.mul t (mapPt ψ' hψ' P) (mapPt ψ' hψ' Q)) →
        (∀ x : ↥Λ, E.act x ≫ φ' = φ' ≫ E₁'.act x) → (∀ x : ↥Λ, E₁'.act x ≫ ψ' = ψ' ≫ E.act x) →
        (∀ hℓ : ((ℓ' : ℚ) : ℍ[ℚ, a, b]) ∈ Λ,
          φ' ≫ ψ' = E.act ⟨((ℓ' : ℚ) : ℍ[ℚ, a, b]), hℓ⟩ ∧ ψ' ≫ φ' = E₁'.act ⟨((ℓ' : ℚ) : ℍ[ℚ, a, b]), hℓ⟩) →
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t E.f),
          mapPt φ' hφ' P = E₁'.L.one t ↔ FactorsThrough K'.levK P) →
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t E.f),
          FactorsThrough E.lev P → FactorsThrough E₁'.lev (mapPt φ' hφ' P)) →
      ∀ (K₁' : E₁.ExtraLevel ℓ'),
        (∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) E₁.f,
          FactorsThrough K₁'.levK x ↔ ∃ y : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) E.f, FactorsThrough K'.levK y ∧ mapPt φ hφ y = x) →
      ∀ (K₁ : E₁'.ExtraLevel ℓ),
        (∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) E₁'.f,
          FactorsThrough K₁.levK x ↔ ∃ y : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) E.f, FactorsThrough K.levK y ∧ mapPt φ' hφ' y = x) →
        FakeEllipticCurve.IsLevelIsogeny ℓ' (⟨E₁, K₁'⟩ : FakeEllipticCurve.WithExtraLevel Λ N ℓ' (AlgebraicClosure ℚ)) d →
        FakeEllipticCurve.IsLevelIsogeny ℓ (⟨E₁', K₁⟩ : FakeEllipticCurve.WithExtraLevel Λ N ℓ (AlgebraicClosure ℚ)) d' →
        FakeEllipticCurve.Iso d d')
    (ℓ ℓ' : HeckeTower.AwayPrime q q') (D : Divisor (AlgebraicClosure ℚ) Fbar) :
    Divisor.correspondence (𝕋.φ (ℓ, 0)) (𝕋.φ (ℓ, 1)) (𝕋.integral (ℓ, 0)) (𝕋.integral (ℓ, 1))
      (Divisor.correspondence (𝕋.φ (ℓ', 0)) (𝕋.φ (ℓ', 1)) (𝕋.integral (ℓ', 0)) (𝕋.integral (ℓ', 1)) D) =
    Divisor.correspondence (𝕋.φ (ℓ', 0)) (𝕋.φ (ℓ', 1)) (𝕋.integral (ℓ', 0)) (𝕋.integral (ℓ', 1))
      (Divisor.correspondence (𝕋.φ (ℓ, 0)) (𝕋.φ (ℓ, 1)) (𝕋.integral (ℓ, 0)) (𝕋.integral (ℓ, 1)) D) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_ModuliTowerWitnessD_correspondence_comm_of_exhaustive_of_swap_of_two_mul_dvd.solution
