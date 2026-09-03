import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isAdmissible_and_isIsomorphic_iff_exists_isIso_of_isArtinianRing
attribute [-instance] instTopologicallyFGOfFiniteType

set_option autoImplicit false

universe u v

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal in

theorem CerednikDrinfeld.SpecialFormal.Rigidified.exists_isAdmissible_and_isIsomorphic_iff_exists_isIso_of_isArtinianRing
    {p : ℕ} [Fact p.Prime] {O : Type v} [CommRing O] (ι : Zp2 p →+* O)
    (Φ : FormalODModule p (O ⧸ pIdeal p O))
    {k : Type u} [Field k] [CharP k p] (ψk : O →+* k)
    (t₀ : Rigidified p Φ k) (ht₀ : t₀.IsAdmissible ι ψk)
    {A : Type u} [CommRing A] [IsLocalRing A] [IsArtinianRing A] (ψA : O →+* A)
    (res : A →+* k) (hres : Function.Surjective res) (hψ : res.comp ψA = ψk) :

    (∀ (X : FormalODModule p A), X.IsSpecial (ψA.comp ι) → X.HasHeight 4 →
      ∀ (v : t₀.X.Hom (X.map res)), v.IsIso →
      ∃ (n : ℕ) (ρ : Series (A ⧸ pIdeal p A)),
        (⟨X, n, ρ⟩ : Rigidified p Φ A).IsAdmissible ι ψA ∧
        ∃ m : ℕ,
          (((⟨X, n, ρ⟩ : Rigidified p Φ A).map res).Xbar.act ((p : Zp2 p) ^ (m + n))).comp
              ((v.toSeries.map (Ideal.Quotient.mk (pIdeal p k))).comp t₀.ρ) =
            (((⟨X, n, ρ⟩ : Rigidified p Φ A).map res).Xbar.act ((p : Zp2 p) ^ (m + t₀.n))).comp
              (((⟨X, n, ρ⟩ : Rigidified p Φ A).map res).ρ)) ∧

    (∀ (t t' : Rigidified p Φ A), t.IsAdmissible ι ψA → t'.IsAdmissible ι ψA →
      ∀ (v : t₀.X.Hom (t.X.map res)) (v' : t₀.X.Hom (t'.X.map res)),
      (∃ m : ℕ,
          ((t.map res).Xbar.act ((p : Zp2 p) ^ (m + t.n))).comp
              ((v.toSeries.map (Ideal.Quotient.mk (pIdeal p k))).comp t₀.ρ) =
            ((t.map res).Xbar.act ((p : Zp2 p) ^ (m + t₀.n))).comp (t.map res).ρ) →
      (∃ m : ℕ,
          ((t'.map res).Xbar.act ((p : Zp2 p) ^ (m + t'.n))).comp
              ((v'.toSeries.map (Ideal.Quotient.mk (pIdeal p k))).comp t₀.ρ) =
            ((t'.map res).Xbar.act ((p : Zp2 p) ^ (m + t₀.n))).comp (t'.map res).ρ) →
      (t.IsIsomorphic t' ↔
        ∃ s : t.X.Hom t'.X, s.IsIso ∧ (s.map res).comp v = v')) ∧

    (∀ (t : Rigidified p Φ A), t.IsAdmissible ι ψA → t₀.IsIsomorphic (t.map res) →
      ∃ (v : t₀.X.Hom (t.X.map res)), v.IsIso ∧
        ∃ m : ℕ,
          ((t.map res).Xbar.act ((p : Zp2 p) ^ (m + t.n))).comp
              ((v.toSeries.map (Ideal.Quotient.mk (pIdeal p k))).comp t₀.ρ) =
            ((t.map res).Xbar.act ((p : Zp2 p) ^ (m + t₀.n))).comp (t.map res).ρ) ∧

    (∀ (t : Rigidified p Φ A), t.IsAdmissible ι ψA → ∀ (v : t₀.X.Hom (t.X.map res)), v.IsIso →
      (∃ m : ℕ,
          ((t.map res).Xbar.act ((p : Zp2 p) ^ (m + t.n))).comp
              ((v.toSeries.map (Ideal.Quotient.mk (pIdeal p k))).comp t₀.ρ) =
            ((t.map res).Xbar.act ((p : Zp2 p) ^ (m + t₀.n))).comp (t.map res).ρ) →
      t₀.IsIsomorphic (t.map res) ∧ (t.map res).IsIsomorphic t₀) ∧

    (∀ (t : Rigidified p Φ A), t.IsAdmissible ι ψA →
      ∀ (A' : Type u) [CommRing A'] [IsLocalRing A'] [IsArtinianRing A'] (ψA' : O →+* A')
        (res' : A' →+* k), Function.Surjective res' → res'.comp ψA' = ψk →
      ∀ (f : A →+* A'), res'.comp f = res → f.comp ψA = ψA' →
        (t.map f).IsAdmissible ι ψA' ∧
        ∀ (v : t₀.X.Hom (t.X.map res)) (v' : t₀.X.Hom ((t.map f).X.map res')),
          v'.toSeries = v.toSeries →
          (∃ m : ℕ,
              ((t.map res).Xbar.act ((p : Zp2 p) ^ (m + t.n))).comp
                  ((v.toSeries.map (Ideal.Quotient.mk (pIdeal p k))).comp t₀.ρ) =
                ((t.map res).Xbar.act ((p : Zp2 p) ^ (m + t₀.n))).comp (t.map res).ρ) →
          ∃ m : ℕ,
            (((t.map f).map res').Xbar.act ((p : Zp2 p) ^ (m + (t.map f).n))).comp
                ((v'.toSeries.map (Ideal.Quotient.mk (pIdeal p k))).comp t₀.ρ) =
              (((t.map f).map res').Xbar.act ((p : Zp2 p) ^ (m + t₀.n))).comp ((t.map f).map res').ρ) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isAdmissible_and_isIsomorphic_iff_exists_isIso_of_isArtinianRing.solution
