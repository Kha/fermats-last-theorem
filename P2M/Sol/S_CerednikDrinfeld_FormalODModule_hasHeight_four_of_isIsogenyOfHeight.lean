import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule

import Theorems.Thm_CerednikDrinfeld_FormalODModule_HasKernelOfDegree_comp
import Theorems.Thm_CerednikDrinfeld_FormalODModule_HasKernelOfDegree_of_comp
import P2M.Util
namespace P2MW.S_CerednikDrinfeld_FormalODModule_hasHeight_four_of_isIsogenyOfHeight
attribute [-instance] instTopologicallyFGOfFiniteType

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem solution
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] [IsNoetherianRing B] (hB : IsNilpotent (p : B))
    (X Y : FormalODModule p B) (ρ : Series B) (h : ℕ)
    (hρ : FormalODModule.IsIsogenyOfHeight X Y ρ h) (hX : X.HasHeight 4) :
    Y.HasHeight 4 := by
  obtain ⟨hhom, hker⟩ := hρ
  have hX0 : ∀ i, MvPowerSeries.constantCoeff (X.act (p : Zp2 p) i) = 0 := (X.isLawHom_act (p : Zp2 p)).1
  have hY0 : ∀ i, MvPowerSeries.constantCoeff (Y.act (p : Zp2 p) i) = 0 := (Y.isLawHom_act (p : Zp2 p)).1

  have hcomp : FormalODModule.HasKernelOfDegree (ρ.comp (X.act (p : Zp2 p))) (p ^ 4 * p ^ h) :=
    CerednikDrinfeld.FormalODModule.HasKernelOfDegree.comp hX0 hhom.1.1 hX hker

  rw [hhom.2.1 (p : Zp2 p), mul_comm] at hcomp

  exact CerednikDrinfeld.FormalODModule.HasKernelOfDegree.of_comp hhom.1.1 hY0 hker hcomp
