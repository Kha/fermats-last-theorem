import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_exists_G_bijective_isActBy_iff_isTwistedAct_wittVector_of_exists_forall_bijective_of_isNoetherianRing
attribute [-instance] instTopologicallyFGOfFiniteType

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.SpecialFormal.ModuliPackage.exists_G_bijective_isActBy_iff_isTwistedAct_wittVector_of_exists_forall_bijective_of_isNoetherianRing
    {r : ℕ} [Fact r.Prime] (k : Type) [Field k] [CharP k r] [IsAlgClosed k]

    [Algebra ℤ_[r] (WittVector r k)]
    (Fr : WittVector r k ≃ₐ[ℤ_[r]] WittVector r k) (hFr : ∀ x : WittVector r k, Fr x = WittVector.frobenius x)
    (vdet : Matrix.GeneralLinearGroup (Fin 2) ℚ_[r] →* Multiplicative ℤ)
    (hvdet : ∀ (g : Matrix.GeneralLinearGroup (Fin 2) ℚ_[r]) (n : ℤ), vdet g = Multiplicative.ofAdd n ↔
      ∃ u : ℤ_[r]ˣ, (Matrix.GeneralLinearGroup.det g : ℚ_[r]) = algebraMap ℤ_[r] ℚ_[r] (u : ℤ_[r]) * (algebraMap ℤ_[r] ℚ_[r] ((r : ℕ) : ℤ_[r])) ^ n)

    (ι : Zp2 r →+* WittVector r k)
    (Φ : FormalODModule r (WittVector r k ⧸ pIdeal r (WittVector r k)))
    (hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal r (WittVector r k))).comp ι))
    (hΦ4 : Φ.HasHeight 4)
    (M : ModuliPackage.{0, 0} r (WittVector r k)) (hM : M.IsZariskiSheaf)
    (η : ∀ (B : Type) [CommRing B] (ψ : WittVector r k →+* B) (hB : IsNilpotent (r : B)),
      Rigidified r Φ B → M.obj B ψ hB)
    (hη : (∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : WittVector r k →+* B) (hB : IsNilpotent (r : B))
          (t t' : Rigidified r Φ B), t.IsAdmissible ι ψ → t'.IsAdmissible ι ψ →
          (η B ψ hB t = η B ψ hB t' ↔ t.IsIsomorphic t')) ∧
      (∀ (B B' : Type) [CommRing B] [CommRing B'] [IsNoetherianRing B] [IsNoetherianRing B'] (ψ : WittVector r k →+* B) (ψ' : WittVector r k →+* B')
          (hB : IsNilpotent (r : B)) (hB' : IsNilpotent (r : B')) (f : B →+* B')
          (hf : f.comp ψ = ψ') (t : Rigidified r Φ B), t.IsAdmissible ι ψ →
          η B' ψ' hB' (t.map f) = M.map hB hB' f hf (η B ψ hB t)) ∧
      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : WittVector r k →+* B) (hB : IsNilpotent (r : B)) (m : M.obj B ψ hB),
          ∃ (n : ℕ) (f : Fin n → B), Ideal.span (Set.range f) = ⊤ ∧
            ∀ (i : Fin n) (L : Type) [CommRing L] [IsNoetherianRing L] [Algebra B L] [IsLocalization.Away (f i) L]
              (hL : IsNilpotent (r : L)),
              ∃ t : Rigidified r Φ L, t.IsAdmissible ι ((algebraMap B L).comp ψ) ∧
                η L ((algebraMap B L).comp ψ) hL t =
                  M.map (ψ' := (algebraMap B L).comp ψ) hB hL (algebraMap B L) rfl m))

    (hmaster :
    ∃ (θ : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[r] B] (ψ : WittVector r k →+* B) (hB : IsNilpotent (r : B)),
        M.obj B ψ hB → OmegaObj (K := ℚ_[r]) (r : ℤ_[r]) B)
      (E : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}) →+* Matrix (Fin 2) (Fin 2) ℚ_[r]),

      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[r] B] (ψ : WittVector r k →+* B) (hB : IsNilpotent (r : B)),
        Function.Bijective (θ B ψ hB)) ∧

      (∀ (B B' : Type) [CommRing B] [CommRing B'] [IsNoetherianRing B] [IsNoetherianRing B'] [Algebra ℤ_[r] B] [Algebra ℤ_[r] B']
        (ψ : WittVector r k →+* B) (ψ' : WittVector r k →+* B')
        (hB : IsNilpotent (r : B)) (hB' : IsNilpotent (r : B')) (f : B →ₐ[ℤ_[r]] B')
        (hf : (f : B →+* B').comp ψ = ψ') (x : M.obj B ψ hB),
        DeligneDatum.IsBaseChange (K := ℚ_[r]) (π := (r : ℤ_[r])) f (θ B ψ hB x)
          (θ B' ψ' hB' (M.map hB hB' (f : B →+* B') hf x))) ∧

      (Function.Injective E ∧
        ∃ m : ℕ,
          (∀ A : Matrix (Fin 2) (Fin 2) ℤ_[r], ∃ e, E e = (r : ℚ_[r]) ^ m • A.map ((↑) : ℤ_[r] → ℚ_[r])) ∧
          (∀ e, ∃ A : Matrix (Fin 2) (Fin 2) ℤ_[r], (r : ℚ_[r]) ^ m • E e = A.map ((↑) : ℤ_[r] → ℚ_[r]))) ∧

      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : WittVector r k →+* B) (t : Rigidified r Φ B), t.IsAdmissible ι ψ →
        ∀ (e : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})) (m' : ℕ),
          FormalODModule.HasKernelOfDegree (e : MvFormalGroup.End Φ.F).toPowerSeries (r ^ (2 * m')) →
          ∃ t' : Rigidified r Φ B,
            t'.IsAdmissible ι (ψ.comp ((WittVector.frobenius : WittVector r k →+* WittVector r k) ^ m')) ∧
            t'.X = t.X ∧
            ∃ c : ℕ,
              (t.Xbar.act ((r : Zp2 r) ^ (c + t.n))).comp
                  (t'.ρ.comp fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) (B ⧸ pIdeal r B)) ^ (r ^ m')) =
                (t.Xbar.act ((r : Zp2 r) ^ (c + t'.n))).comp
                  (t.ρ.comp (Series.map (residueMap ψ) (e : MvFormalGroup.End Φ.F).toPowerSeries))) ∧

      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[r] B] (ψ : WittVector r k →+* B) (hB : IsNilpotent (r : B))
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
              (η B (ψ.comp ((WittVector.frobenius : WittVector r k →+* WittVector r k) ^ m')) hB t'))) ∧

      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : WittVector r k →+* B) (t : Rigidified r Φ B), t.IsAdmissible ι ψ →
          ∃ t' : Rigidified r Φ B,
            t'.IsAdmissible ι (ψ.comp (WittVector.frobenius : WittVector r k →+* WittVector r k)) ∧
            t'.X.F = t.X.F ∧ t'.X.varpi = t.X.varpi ∧ (∀ a, t'.X.act a = t.X.act (WittVector.frobenius a)) ∧
            ∃ c : ℕ,
              (t.Xbar.act ((r : Zp2 r) ^ (c + t.n))).comp
                  (t'.ρ.comp fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) (B ⧸ pIdeal r B)) ^ r) =
                (t.Xbar.act ((r : Zp2 r) ^ (c + t'.n))).comp (t.ρ.comp (Φ.varpi.map (residueMap ψ)))) ∧

      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[r] B] (ψ : WittVector r k →+* B) (hB : IsNilpotent (r : B))
        (t t' : Rigidified r Φ B), t.IsAdmissible ι ψ →
          t'.IsAdmissible ι (ψ.comp (WittVector.frobenius : WittVector r k →+* WittVector r k)) →
          t'.X.F = t.X.F → t'.X.varpi = t.X.varpi → (∀ a, t'.X.act a = t.X.act (WittVector.frobenius a)) →
          (∃ c : ℕ,
              (t.Xbar.act ((r : Zp2 r) ^ (c + t.n))).comp
                  (t'.ρ.comp fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) (B ⧸ pIdeal r B)) ^ r) =
                (t.Xbar.act ((r : Zp2 r) ^ (c + t'.n))).comp (t.ρ.comp (Φ.varpi.map (residueMap ψ)))) →
          θ B (ψ.comp (WittVector.frobenius : WittVector r k →+* WittVector r k)) hB
              (η B (ψ.comp (WittVector.frobenius : WittVector r k →+* WittVector r k)) hB t') =
            θ B ψ hB (η B ψ hB t)))
    :
    ∃
      (E₀ : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}) →+* Matrix (Fin 2) (Fin 2) ℚ_[r])
      (_ : Function.Injective E₀ ∧
        ∃ m : ℕ,
          (∀ A : Matrix (Fin 2) (Fin 2) ℤ_[r], ∃ e, E₀ e = (r : ℚ_[r]) ^ m • A.map (algebraMap ℤ_[r] ℚ_[r])) ∧
          (∀ e, ∃ A : Matrix (Fin 2) (Fin 2) ℤ_[r], (r : ℚ_[r]) ^ m • E₀ e = A.map (algebraMap ℤ_[r] ℚ_[r])))
      (e : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[r] B], IsNilpotent (algebraMap ℤ_[r] B ((r : ℕ) : ℤ_[r])) → (ModuliPackage.G ℤ_[r] M).obj B → (AlgFunctor.prod (AlgFunctor.corep (WittVector r k)) (Omega ℚ_[r] ((r : ℕ) : ℤ_[r]))).obj B),

      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[r] B] (B' : Type) [CommRing B'] [IsNoetherianRing B'] [Algebra ℤ_[r] B'] (hB : IsNilpotent (algebraMap ℤ_[r] B ((r : ℕ) : ℤ_[r]))) (hB' : IsNilpotent (algebraMap ℤ_[r] B' ((r : ℕ) : ℤ_[r])))
          (φ : B →ₐ[ℤ_[r]] B') (x : (ModuliPackage.G ℤ_[r] M).obj B), e B' hB' ((ModuliPackage.G ℤ_[r] M).map φ x) = (AlgFunctor.prod (AlgFunctor.corep (WittVector r k)) (Omega ℚ_[r] ((r : ℕ) : ℤ_[r]))).map φ (e B hB x)) ∧

      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[r] B] (hB : IsNilpotent (algebraMap ℤ_[r] B ((r : ℕ) : ℤ_[r]))), Function.Bijective (e B hB)) ∧

      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[r] B] (hB : IsNilpotent (algebraMap ℤ_[r] B ((r : ℕ) : ℤ_[r]))) (x : (ModuliPackage.G ℤ_[r] M).obj B), (e B hB x).1 = x.ψ) ∧

      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[r] B] (hB : IsNilpotent (algebraMap ℤ_[r] B ((r : ℕ) : ℤ_[r]))) (g : Matrix.GeneralLinearGroup (Fin 2) ℚ_[r]) (x x' : (ModuliPackage.G ℤ_[r] M).obj B),
          ModuliPackage.G.IsActBy ι Φ η Fr E₀ g x x' ↔ OmegaNr.IsTwistedAct ((r : ℕ) : ℤ_[r]) (WittVector r k) Fr vdet B g (e B hB x) (e B hB x')) ∧

      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[r] B] (hB : IsNilpotent (algebraMap ℤ_[r] B ((r : ℕ) : ℤ_[r]))) (x x' : (ModuliPackage.G ℤ_[r] M).obj B),
          ModuliPackage.G.IsPiTranslate ι Φ η Fr x x' → e B hB x' = (frobTwist (WittVector r k) Fr 1 (e B hB x).1, (e B hB x).2)) ∧

      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[r] B] (x : (ModuliPackage.G ℤ_[r] M).obj B), ∃ x' : (ModuliPackage.G ℤ_[r] M).obj B, ModuliPackage.G.IsPiTranslate ι Φ η Fr x x') := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_exists_G_bijective_isActBy_iff_isTwistedAct_wittVector_of_exists_forall_bijective_of_isNoetherianRing.solution
