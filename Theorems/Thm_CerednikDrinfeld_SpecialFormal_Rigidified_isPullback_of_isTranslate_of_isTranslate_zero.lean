import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_SpecialFormal_Rigidified_isPullback_of_isTranslate_of_isTranslate_zero

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.SpecialFormal.Rigidified.isPullback_of_isTranslate_of_isTranslate_zero
    {r : ℕ} [Fact r.Prime] (k : Type) [Field k] [CharP k r] [IsAlgClosed k]
    [Algebra ℤ_[r] (WittVector r k)]
    (Fr : WittVector r k ≃ₐ[ℤ_[r]] WittVector r k) (hFr : ∀ x : WittVector r k, Fr x = WittVector.frobenius x)
    (ι : Zp2 r →+* WittVector r k)
    (Φ : FormalODModule r (WittVector r k ⧸ pIdeal r (WittVector r k)))
    (hΦ4 : Φ.HasHeight 4)
    (M : ModuliPackage.{0, 0} r (WittVector r k))
    (η : ∀ (B : Type) [CommRing B] (ψ : WittVector r k →+* B) (hB : IsNilpotent (r : B)),
      Rigidified r Φ B → M.obj B ψ hB)
    (hη : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : WittVector r k →+* B) (hB : IsNilpotent (r : B))
      (t t' : Rigidified r Φ B), t.IsAdmissible ι ψ → t'.IsAdmissible ι ψ →
      (η B ψ hB t = η B ψ hB t' ↔ t.IsIsomorphic t'))
    (θ : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[r] B] (ψ : WittVector r k →+* B) (hB : IsNilpotent (r : B)),
      M.obj B ψ hB → OmegaObj (K := ℚ_[r]) (r : ℤ_[r]) B)
    (E : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}) →+* Matrix (Fin 2) (Fin 2) ℚ_[r])

    (hGLdef : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : WittVector r k →+* B) (t : Rigidified r Φ B), t.IsAdmissible ι ψ →
      ∀ (e : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})) (m' : ℕ),
        FormalODModule.HasKernelOfDegree (e : MvFormalGroup.End Φ.F).toPowerSeries (r ^ (2 * m')) →
        ∃ t' : Rigidified r Φ B,
          t'.IsAdmissible ι (ψ.comp ((WittVector.frobenius : WittVector r k →+* WittVector r k) ^ m')) ∧
          t'.X = t.X ∧
          ∃ c : ℕ,
            (t.Xbar.act ((r : Zp2 r) ^ (c + t.n))).comp
                (t'.ρ.comp fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) (B ⧸ pIdeal r B)) ^ (r ^ m')) =
              (t.Xbar.act ((r : Zp2 r) ^ (c + t'.n))).comp
                (t.ρ.comp (Series.map (residueMap ψ) (e : MvFormalGroup.End Φ.F).toPowerSeries)))

    (hGLeq : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[r] B] (ψ : WittVector r k →+* B) (hB : IsNilpotent (r : B))
      (e : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})) (m' : ℕ),
      FormalODModule.HasKernelOfDegree (e : MvFormalGroup.End Φ.F).toPowerSeries (r ^ (2 * m')) →
      ∀ (g : Matrix.GeneralLinearGroup (Fin 2) ℚ_[r]), (g : Matrix (Fin 2) (Fin 2) ℚ_[r]) = E e →
      ∀ (t t' : Rigidified r Φ B), t.IsAdmissible ι ψ →
        t'.IsAdmissible ι (ψ.comp ((WittVector.frobenius : WittVector r k →+* WittVector r k) ^ m')) →
        t'.X = t.X →
        (∃ c : ℕ,
            (t.Xbar.act ((r : Zp2 r) ^ (c + t.n))).comp
                (t'.ρ.comp fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) (B ⧸ pIdeal r B)) ^ (r ^ m')) =
              (t.Xbar.act ((r : Zp2 r) ^ (c + t'.n))).comp
                (t.ρ.comp (Series.map (residueMap ψ) (e : MvFormalGroup.End Φ.F).toPowerSeries))) →
        DeligneDatum.IsPullback (K := ℚ_[r]) (π := (r : ℤ_[r])) B g (θ B ψ hB (η B ψ hB t))
          (θ B (ψ.comp ((WittVector.frobenius : WittVector r k →+* WittVector r k) ^ m')) hB
            (η B (ψ.comp ((WittVector.frobenius : WittVector r k →+* WittVector r k) ^ m')) hB t')))

    (L : Type) [CommRing L] [IsNoetherianRing L] [Algebra ℤ_[r] L] (ψ : WittVector r k →+* L) (hL : IsNilpotent (r : L))
    (e : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})) (kk m' : ℕ)
    (he : FormalODModule.HasKernelOfDegree (e : MvFormalGroup.End Φ.F).toPowerSeries (r ^ (2 * m')))
    (g₀ : Matrix.GeneralLinearGroup (Fin 2) ℚ_[r]) (hg₀ : (g₀ : Matrix (Fin 2) (Fin 2) ℚ_[r]) = E e)
    (t t' : Rigidified r Φ L) (ht : t.IsAdmissible ι ψ)
    (ht' : t'.IsAdmissible ι
      (ψ.comp (((Fr ^ ((m' : ℤ) - 2 * kk) : WittVector r k ≃ₐ[ℤ_[r]] WittVector r k) :
        WittVector r k →ₐ[ℤ_[r]] WittVector r k) : WittVector r k →+* WittVector r k)))
    (htt' : Rigidified.IsTranslate (e : MvFormalGroup.End Φ.F).toPowerSeries kk m' ψ t t') :
    DeligneDatum.IsPullback (K := ℚ_[r]) (π := (r : ℤ_[r])) L g₀ (θ L ψ hL (η L ψ hL t))
      (θ L (ψ.comp (((Fr ^ ((m' : ℤ) - 2 * kk) : WittVector r k ≃ₐ[ℤ_[r]] WittVector r k) :
          WittVector r k →ₐ[ℤ_[r]] WittVector r k) : WittVector r k →+* WittVector r k)) hL
        (η L (ψ.comp (((Fr ^ ((m' : ℤ) - 2 * kk) : WittVector r k ≃ₐ[ℤ_[r]] WittVector r k) :
          WittVector r k →ₐ[ℤ_[r]] WittVector r k) : WittVector r k →+* WittVector r k)) hL t')) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_isPullback_of_isTranslate_of_isTranslate_zero.solution
