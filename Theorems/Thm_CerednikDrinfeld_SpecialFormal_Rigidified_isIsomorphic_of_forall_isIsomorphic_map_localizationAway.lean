import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_SpecialFormal_Rigidified_isIsomorphic_of_forall_isIsomorphic_map_localizationAway

set_option autoImplicit false

universe u v

open MvPowerSeries CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.SpecialFormal.Rigidified.isIsomorphic_of_forall_isIsomorphic_map_localizationAway
    {p : ℕ} [Fact p.Prime] {O : Type v} [CommRing O] {Φ : FormalODModule p (O ⧸ pIdeal p O)}
    (ι : Zp2 p →+* O) {B : Type u} [CommRing B] (ψ : O →+* B) (hB : IsNilpotent (p : B)) [IsNoetherianRing B]
    (t t' : Rigidified p Φ B) (ht : t.IsAdmissible ι ψ) (ht' : t'.IsAdmissible ι ψ)
    (n : ℕ) (f : Fin n → B) (hf : Ideal.span (Set.range f) = ⊤)
    (hloc : ∀ i, (t.map (algebraMap B (Localization.Away (f i)))).IsIsomorphic
      (t'.map (algebraMap B (Localization.Away (f i))))) :
    t.IsIsomorphic t' := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_isIsomorphic_of_forall_isIsomorphic_map_localizationAway.solution
