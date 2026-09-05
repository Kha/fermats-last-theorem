import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import P2M.Util
namespace P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_exists_isAdmissible_eta_eq_of_isLocalRing

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

namespace P2mOST0

theorem exists_isUnit_of_span_range_eq_top {B : Type*} [CommRing B] [IsLocalRing B] {n : ℕ} (f : Fin n → B)
    (h : Ideal.span (Set.range f) = ⊤) : ∃ i, IsUnit (f i) := by
  by_contra hne
  push_neg at hne
  have hle : Ideal.span (Set.range f) ≤ IsLocalRing.maximalIdeal B := by
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    exact (IsLocalRing.mem_maximalIdeal _).mpr (hne i)
  rw [h] at hle
  exact (IsLocalRing.maximalIdeal.isMaximal B).ne_top (top_le_iff.mp hle)

end P2mOST0

theorem solution
    {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] (ι : Zp2 p →+* O)
    (Φ : FormalODModule p (O ⧸ pIdeal p O))
    (M : ModuliPackage.{0, 0} p O)
    (η : ∀ (B : Type) [CommRing B] (ψ : O →+* B) (hB : IsNilpotent (p : B)), Rigidified p Φ B → M.obj B ψ hB)
    (hη : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : O →+* B) (hB : IsNilpotent (p : B)) (m : M.obj B ψ hB),
      ∃ (n : ℕ) (f : Fin n → B), Ideal.span (Set.range f) = ⊤ ∧
        ∀ (i : Fin n) (L : Type) [CommRing L] [IsNoetherianRing L] [Algebra B L] [IsLocalization.Away (f i) L]
          (hL : IsNilpotent (p : L)),
          ∃ t : Rigidified p Φ L, t.IsAdmissible ι ((algebraMap B L).comp ψ) ∧
            η L ((algebraMap B L).comp ψ) hL t = M.map (ψ' := (algebraMap B L).comp ψ) hB hL (algebraMap B L) rfl m)
    (B : Type) [CommRing B] [IsNoetherianRing B] [IsLocalRing B] (ψ : O →+* B) (hB : IsNilpotent (p : B))
    (m : M.obj B ψ hB) :
    ∃ t : Rigidified p Φ B, t.IsAdmissible ι ψ ∧ η B ψ hB t = m := by
  obtain ⟨n, f, hspan, hloc⟩ := hη B ψ hB m
  obtain ⟨i, hi⟩ := P2mOST0.exists_isUnit_of_span_range_eq_top f hspan
  haveI : IsLocalization.Away (f i) B := IsLocalization.away_of_isUnit_of_bijective B hi Function.bijective_id
  obtain ⟨t, ht, hηt⟩ := hloc i B hB
  exact ⟨t, ht, hηt.trans (M.map_id hB m)⟩

