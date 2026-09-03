import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isAdmissible_isIsomorphic_eta_eq_of_isODHom_comp_eq_id

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.SpecialFormal.Rigidified.exists_isAdmissible_isIsomorphic_eta_eq_of_isODHom_comp_eq_id
    {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] (ι : Zp2 p →+* O) {Φ : FormalODModule p (O ⧸ pIdeal p O)}
    {M : ModuliPackage.{0, 0} p O}
    (η : ∀ (B : Type) [CommRing B] (ψ : O →+* B) (hB : IsNilpotent (p : B)), Rigidified p Φ B → M.obj B ψ hB)
    (hη : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : O →+* B) (hB : IsNilpotent (p : B))
        (t t' : Rigidified p Φ B), t.IsAdmissible ι ψ → t'.IsAdmissible ι ψ →
        (η B ψ hB t = η B ψ hB t' ↔ t.IsIsomorphic t'))

    (B : Type) [CommRing B] [IsNoetherianRing B] (χ : O →+* B) (hBp : IsNilpotent (p : B))
    (X X' : FormalODModule p B) (u v : Series B)
    (hu : FormalODModule.IsODHom X X' u) (hv : FormalODModule.IsODHom X' X v)
    (hvu : v.comp u = Series.id B) (huv : u.comp v = Series.id B)
    (t' : Rigidified p Φ B) (ht'X : t'.X = X') (hadm' : t'.IsAdmissible ι χ)
    (hXs : X.IsSpecial (structureMap ι χ)) (hX4 : X.HasHeight 4) :
    ∃ t : Rigidified p Φ B,
      t.X = X ∧ t.n = t'.n ∧
      t.ρ = (Series.map (Ideal.Quotient.mk (pIdeal p B)) v).comp t'.ρ ∧
      t.IsAdmissible ι χ ∧ t'.IsIsomorphic t ∧ t.IsIsomorphic t' ∧
      η B χ hBp t = η B χ hBp t' := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isAdmissible_isIsomorphic_eta_eq_of_isODHom_comp_eq_id.solution
