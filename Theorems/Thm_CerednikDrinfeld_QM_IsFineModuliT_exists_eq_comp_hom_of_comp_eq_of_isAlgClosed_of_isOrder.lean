import Definitions.Def_CerednikDrinfeld_QMCoarseModuli
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMFineModuliT
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_IsFineModuliT_exists_eq_comp_hom_of_comp_eq_of_isAlgClosed_of_isOrder

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.IsFineModuliT.exists_eq_comp_hom_of_comp_eq_of_isAlgClosed_of_isOrder
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ) {N : ℕ} {𝒪 : Type} [CommRing 𝒪]
    (n ℓ : ℕ)
    (𝒴 : Scheme.{0}) (g : 𝒴 ⟶ Spec (CommRingCat.of 𝒪))
    (ptT : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithExtraLevel Λ N ℓ S → SchemeHomOver s g)
    (h𝒴 : IsCoarseModuliT Λ N ℓ 𝒴 g ptT)
    (M : Scheme.{0}) (fM : M ⟶ Spec (CommRingCat.of 𝒪))
    (ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N n S → SchemeHomOver s fM)
    (Mℓ : Scheme.{0}) (fMℓ : Mℓ ⟶ Spec (CommRingCat.of 𝒪))
    (ptFℓ : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) (u : FakeEllipticCurve.WithFullLevel Λ N n S),
      u.1.ExtraLevel ℓ → SchemeHomOver s fMℓ)
    (hMℓ : IsFineModuliT Λ N n ℓ Mℓ fMℓ ptFℓ)
    (G : Type) [Group G] (χ : G → ↥Λ) (ρ : G →* Aut M) (hρ : IsLevelTwistAction Λ N n M fM ptF G ρ χ) (ρℓ : G →* Aut Mℓ)
    (hρℓtw : ∀ (h : G) (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
      (u u' : FakeEllipticCurve.WithFullLevel Λ N n S) (C : u.1.ExtraLevel ℓ) (C' : u'.1.ExtraLevel ℓ)
      (e : u.1.A ≅ u'.1.A) (he : e.hom ≫ u'.1.f = u.1.f),
      FakeEllipticCurve.WithFullLevel.IsTwistVia (χ h) u u' e he →
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t u.1.f),
          FactorsThrough C.levK P ↔ FactorsThrough C'.levK (mapPt e.hom he P)) →
        (ptFℓ S s u' C').1 = (ptFℓ S s u C).1 ≫ (ρℓ h).hom)
    (pℓ : Mℓ ⟶ 𝒴)
    (hpℓ : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) (u : FakeEllipticCurve.WithFullLevel Λ N n S)
      (C : u.1.ExtraLevel ℓ), (ptFℓ S s u C).1 ≫ pℓ = (ptT S s ⟨u.1, C⟩).1)
    (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of 𝒪))
    (y y' : SchemeHomOver s fMℓ) (hyy' : y.1 ≫ pℓ = y'.1 ≫ pℓ) :
    ∃ g : G, y'.1 = y.1 ≫ (ρℓ g).hom := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_IsFineModuliT_exists_eq_comp_hom_of_comp_eq_of_isAlgClosed_of_isOrder.solution
