import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isAdmissible_mk_and_act_pow_comp_map_eq_of_map_eq_of_surjective_of_isNilpotent
attribute [-instance] instTopologicallyFGOfFiniteType

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.SpecialFormal.Rigidified.exists_isAdmissible_mk_and_act_pow_comp_map_eq_of_map_eq_of_surjective_of_isNilpotent
    {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] (ι : Zp2 p →+* O) (Φ : FormalODModule p (O ⧸ pIdeal p O))
    {R S : Type} [CommRing R] [CommRing S] [IsNoetherianRing R] [IsNoetherianRing S]
    (π : R →+* S) (hπ : Function.Surjective π) (hker : IsNilpotent (RingHom.ker π)) (hR : IsNilpotent (p : R))
    (ψR : O →+* R) (ψS : O →+* S) (hψ : π.comp ψR = ψS)
    (X : FormalODModule p R) (hXs : X.IsSpecial (structureMap ι ψR)) (hX4 : X.HasHeight 4)
    (t' : Rigidified p Φ S) (ht' : t'.IsAdmissible ι ψS) (hX : X.map π = t'.X) :
    ∃ (n : ℕ) (ρ : Series (R ⧸ pIdeal p R)),
      (⟨X, n, ρ⟩ : Rigidified p Φ R).IsAdmissible ι ψR ∧
      ∃ m : ℕ, (t'.Xbar.act ((p : Zp2 p) ^ (m + t'.n))).comp (ρ.map (reduceMap π)) =
        (t'.Xbar.act ((p : Zp2 p) ^ (m + n))).comp t'.ρ := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isAdmissible_mk_and_act_pow_comp_map_eq_of_map_eq_of_surjective_of_isNilpotent.solution
