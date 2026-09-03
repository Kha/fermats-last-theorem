import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG
import Definitions.Def_CerednikDrinfeld_PeriodMap
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadrupleRelations
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_nsmul_nMap_rigidNum_translate_eq_nsmul_rigidNum_mulVec

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

theorem CerednikDrinfeld.SpecialFormal.Rigidified.exists_nsmul_nMap_rigidNum_translate_eq_nsmul_rigidNum_mulVec
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
    (ι : Zp2 p →+* WittVector p k)
    (Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
    (hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι)) (hΦ4 : Φ.HasHeight 4)
    (hcΦ : IsCompl (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0) (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
    (hrΦ : ∀ (L : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).M →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
      (hL : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).IsCanonicalLMap L),
      Set.BijOn rΦ Set.univ ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).etaPiece L hL.isCartierLMap.map_verschiebung 0 : Set _))
    {B : Type} [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[p] B]
    (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B))
    (E : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}) →+* Matrix (Fin 2) (Fin 2) ℚ_[p]) (m : ℕ)
    (hEinj : Function.Injective E)
    (hEord : ∀ e, ∃ A : Matrix (Fin 2) (Fin 2) ℤ_[p], (p : ℚ_[p]) ^ m • E e = A.map ((↑) : ℤ_[p] → ℚ_[p]))
    (hEcompat : (∀ (e : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})) (A : Matrix (Fin 2) (Fin 2) ℤ_[p]),
        (p : ℚ_[p]) ^ m • E e = A.map ((↑) : ℤ_[p] → ℚ_[p]) →
        ∀ (Ne : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod),
          (∀ x : MvFormalGroup.CartierModule p Φ.F × (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).Sigma,
            Ne ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMk x) =
              (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMk
                (MvFormalGroup.CartierModule.endAct (e : MvFormalGroup.End Φ.F) x.1,
                 (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).toSigma
                   (MvFormalGroup.CartierModule.endAct (e : MvFormalGroup.End Φ.F)
                     ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).ofSigma x.2)))) →
          ∀ w : Fin 2 → ℤ_[p], p ^ m • Ne (rΦ w) = rΦ (A.mulVec w)))
    (e : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})) (m' : ℕ)
    (hker : FormalODModule.HasKernelOfDegree (e : MvFormalGroup.End Φ.F).toPowerSeries (p ^ (2 * m')))
    (g : Matrix.GeneralLinearGroup (Fin 2) ℚ_[p]) (hg : (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) = E e)
    (A : Matrix (Fin 2) (Fin 2) ℤ_[p]) (hA : (p : ℚ_[p]) ^ m • E e = A.map ((↑) : ℤ_[p] → ℚ_[p]))
    (t : Rigidified p Φ B) (ht : t.IsAdmissible ι ψ) (n' : ℕ) (ρ' : Series (B ⧸ pIdeal p B))
    (ht' : ({ X := t.X, n := n', ρ := ρ' } : Rigidified p Φ B).IsAdmissible ι (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')))
    (htr : Rigidified.IsTranslate (e : MvFormalGroup.End Φ.F).toPowerSeries 0 m' ψ t ({ X := t.X, n := n', ρ := ρ' } : Rigidified p Φ B)) :
    ∃ c : ℕ, ∀ (hOD : FormalODModule.IsODHom (t.Φbar ψ) t.Xbar t.ρ)
      (hOD' : FormalODModule.IsODHom (({ X := t.X, n := n', ρ := ρ' } : Rigidified p Φ B).Φbar (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m'))) t.Xbar ρ')
      {S : Type} [CommRing S] (f : B →+* S)
      (hcb : t.IsGradedSbar ι ψ f)
      (hcΦf : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ f) (hcΦf' : Rigidified.IsGradedPhiS (Φ := Φ) ι (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')) f)
      (NV : ((t.XbarS f).toGradedCartierModuleData (Rigidified.jSbar ι ψ f) hcb).NMod →+ ((t.XbarS f).toGradedCartierModuleData (Rigidified.jSbar ι ψ f) hcb).NMod)
      (hNV : ∀ x : MvFormalGroup.CartierModule p (t.XbarS f).F × MvFormalGroup.CartierModule p (t.XbarS f).F,
        NV (((t.XbarS f).toGradedCartierModuleData (Rigidified.jSbar ι ψ f) hcb).nMk x) = ((t.XbarS f).toGradedCartierModuleData (Rigidified.jSbar ι ψ f) hcb).nMk ((MvFormalGroup.CartierModule.verschiebungInt)^[m'] x.1,
          (MvFormalGroup.CartierModule.verschiebungInt)^[m'] x.2))
      (w : Fin 2 → ℤ_[p]),
      p ^ (c + t.n + m) • NV (((Rigidified.PhibarS (Φ := Φ) (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')) f).toGradedCartierModuleData (Rigidified.jPhiS ι (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')) f) hcΦf').nMap ((t.XbarS f).toGradedCartierModuleData (Rigidified.jSbar ι ψ f) hcb)
            (Rigidified.rhoC (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')) ({ X := t.X, n := n', ρ := ρ' } : Rigidified p Φ B) hOD'.1 f)
            (Rigidified.rhoC_verschiebungInt (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')) ({ X := t.X, n := n', ρ := ρ' } : Rigidified p Φ B) hOD'.1 f)
            (Rigidified.rhoC_endAct_varpiEnd (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')) ({ X := t.X, n := n', ρ := ρ' } : Rigidified p Φ B) hOD' f)
          ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMap ((Rigidified.PhibarS (Φ := Φ) (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')) f).toGradedCartierModuleData (Rigidified.jPhiS ι (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')) f) hcΦf')
            (Rigidified.bcPhi (Φ := Φ) (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')) f) (Rigidified.bcPhi_verschiebungInt (Φ := Φ) (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')) f)
            (Rigidified.bcPhi_endAct_varpiEnd (Φ := Φ) (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')) f) (rΦ w))) =
        p ^ (c + n') • t.rigidNum ι hcΦ rΦ ψ hOD f hcb hcΦf (A.mulVec w) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_nsmul_nMap_rigidNum_translate_eq_nsmul_rigidNum_mulVec.solution
