import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Theorems.Thm_CerednikDrinfeld_FormalODModule_IsSpecial_map
import Theorems.Thm_CerednikDrinfeld_FormalODModule_hasKernelOfDegree_map
import P2M.Util
namespace P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_IsAdmissible_map_ringHom

set_option autoImplicit false

universe u v

open MvPowerSeries CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem solution
    {p : ℕ} [Fact p.Prime] {O : Type v} [CommRing O] {Φ : FormalODModule p (O ⧸ pIdeal p O)}
    (ι : Zp2 p →+* O) {B B' : Type u} [CommRing B] [IsNoetherianRing B] [CommRing B']
    (ψ : O →+* B) (g : B →+* B') (t : Rigidified p Φ B) (ht : t.IsAdmissible ι ψ) :
    (t.map g).IsAdmissible ι (g.comp ψ) := by
  have hXbar : (t.map g).Xbar = t.Xbar.map (reduceMap g) := by
    show (t.X.map g).map (Ideal.Quotient.mk (pIdeal p B')) = (t.X.map _).map _
    rw [FormalODModule.map_map, FormalODModule.map_map]
    congr 1
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact CerednikDrinfeld.FormalODModule.IsSpecial.map (structureMap ι ψ) g t.X ht.1
  · exact CerednikDrinfeld.FormalODModule.hasKernelOfDegree_map g (t.X.act (p : Zp2 p))
      (t.X.isLawHom_act _).1 ht.2.1
  · have := ht.2.2.1.map (reduceMap g)
    rw [Rigidified.Φbar_map, hXbar]
    exact this
  · exact CerednikDrinfeld.FormalODModule.hasKernelOfDegree_map (reduceMap g) t.ρ ht.constantCoeff_ρ ht.2.2.2
