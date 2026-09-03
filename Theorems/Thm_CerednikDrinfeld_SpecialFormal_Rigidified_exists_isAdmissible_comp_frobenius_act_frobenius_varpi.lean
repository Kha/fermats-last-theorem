import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isAdmissible_comp_frobenius_act_frobenius_varpi
attribute [-instance] instTopologicallyFGOfFiniteType

set_option autoImplicit false

universe u

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.SpecialFormal.Rigidified.exists_isAdmissible_comp_frobenius_act_frobenius_varpi
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] [PerfectRing k p]
    (ι : Zp2 p →+* WittVector p k)
    (Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k))) (hΦ4 : Φ.HasHeight 4)
    (B : Type u) [CommRing B] (ψ : WittVector p k →+* B) (t : Rigidified p Φ B)
    (ht : t.IsAdmissible ι ψ) :
    ∃ t' : Rigidified p Φ B,
      t'.IsAdmissible ι (ψ.comp (WittVector.frobenius : WittVector p k →+* WittVector p k)) ∧
      t'.X.F = t.X.F ∧ t'.X.varpi = t.X.varpi ∧ (∀ a, t'.X.act a = t.X.act (WittVector.frobenius a)) ∧
      ∃ c : ℕ,
        (t.Xbar.act ((p : Zp2 p) ^ (c + t.n))).comp
            (t'.ρ.comp fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) (B ⧸ pIdeal p B)) ^ p) =
          (t.Xbar.act ((p : Zp2 p) ^ (c + t'.n))).comp (t.ρ.comp (Φ.varpi.map (residueMap ψ))) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isAdmissible_comp_frobenius_act_frobenius_varpi.solution
