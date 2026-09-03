import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isAdmissible_comp_frobenius_pow_of_hasKernelOfDegree
attribute [-instance] instTopologicallyFGOfFiniteType

set_option autoImplicit false

universe u

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.SpecialFormal.Rigidified.exists_isAdmissible_comp_frobenius_pow_of_hasKernelOfDegree
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] [PerfectRing k p]
    (ι : Zp2 p →+* WittVector p k)
    (Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k))) (hΦ4 : Φ.HasHeight 4)
    (B : Type u) [CommRing B] (ψ : WittVector p k →+* B) (t : Rigidified p Φ B)
    (ht : t.IsAdmissible ι ψ)
    (e : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})) (m' : ℕ)
    (he : FormalODModule.HasKernelOfDegree (e : MvFormalGroup.End Φ.F).toPowerSeries (p ^ (2 * m'))) :
    ∃ t' : Rigidified p Φ B,
      t'.IsAdmissible ι (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')) ∧
      t'.X = t.X ∧
      ∃ c : ℕ,
        (t.Xbar.act ((p : Zp2 p) ^ (c + t.n))).comp
            (t'.ρ.comp fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) (B ⧸ pIdeal p B)) ^ (p ^ m')) =
          (t.Xbar.act ((p : Zp2 p) ^ (c + t'.n))).comp
            (t.ρ.comp (Series.map (residueMap ψ) (e : MvFormalGroup.End Φ.F).toPowerSeries)) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isAdmissible_comp_frobenius_pow_of_hasKernelOfDegree.solution
