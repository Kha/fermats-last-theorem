import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_exists_G_bijective_isActBy_iff_isTwistedAct_of_ringEquiv_frame_of_isNoetherianRing

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.SpecialFormal.ModuliPackage.exists_G_bijective_isActBy_iff_isTwistedAct_of_ringEquiv_frame_of_isNoetherianRing
    {r : ℕ} [Fact r.Prime]

    (𝒪 : Type) [CommRing 𝒪] (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀] (π : 𝒪)
    (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)
    (vdet : Matrix.GeneralLinearGroup (Fin 2) K₀ →* Multiplicative ℤ)
    (𝒪' : Type) [CommRing 𝒪'] (K₀' : Type) [Field K₀'] [Algebra 𝒪' K₀'] (π' : 𝒪')
    (Onr' : Type) [CommRing Onr'] [Algebra 𝒪' Onr'] (Fr' : Onr' ≃ₐ[𝒪'] Onr')
    (vdet' : Matrix.GeneralLinearGroup (Fin 2) K₀' →* Multiplicative ℤ)

    (eb : 𝒪 ≃+* 𝒪') (eK : K₀ ≃+* K₀') (hcomm : ∀ x : 𝒪, eK (algebraMap 𝒪 K₀ x) = algebraMap 𝒪' K₀' (eb x))
    (π₁ : 𝒪') (hπ₁ : eb π = π₁) (hspan : Ideal.span {π₁} = Ideal.span {π'})
    (eO : Onr ≃+* Onr') (heO : ∀ x : 𝒪, eO (algebraMap 𝒪 Onr x) = algebraMap 𝒪' Onr' (eb x))
    (hFr : ∀ y, eO (Fr y) = Fr' (eO y))
    (hv : ∀ g, vdet' (Matrix.GeneralLinearGroup.map eK.toRingHom g) = vdet g)

    (hΨ :
      ∃ (Ψ : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] [Algebra 𝒪' B],
          (∀ x : 𝒪, algebraMap 𝒪 B x = algebraMap 𝒪' B (eb x)) →
            (OmegaNrObj (K := K₀) π Onr B ≃ OmegaNrObj (K := K₀') π₁ Onr' B)),
        (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] [Algebra 𝒪' B]
            (hB : ∀ x : 𝒪, algebraMap 𝒪 B x = algebraMap 𝒪' B (eb x))
            (x : OmegaNrObj (K := K₀) π Onr B) (y : Onr'), (Ψ B hB x).1 y = x.1 (eO.symm y)) ∧
        (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] [Algebra 𝒪' B]
            (hB : ∀ x : 𝒪, algebraMap 𝒪 B x = algebraMap 𝒪' B (eb x))
            (g : Matrix.GeneralLinearGroup (Fin 2) K₀) (x x' : OmegaNrObj (K := K₀) π Onr B),
          OmegaNr.IsTwistedAct π₁ Onr' Fr' vdet' B (Matrix.GeneralLinearGroup.map eK.toRingHom g) (Ψ B hB x) (Ψ B hB x') ↔
            OmegaNr.IsTwistedAct π Onr Fr vdet B g x x') ∧
        (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] [Algebra 𝒪' B]
            (hB : ∀ x : 𝒪, algebraMap 𝒪 B x = algebraMap 𝒪' B (eb x))
            (g : Matrix.GeneralLinearGroup (Fin 2) K₀) (x x' : OmegaNrObj (K := K₀) π Onr B),
          DeligneDatum.IsPullback (K := K₀') (π := π₁) B (Matrix.GeneralLinearGroup.map eK.toRingHom g) (Ψ B hB x).2 (Ψ B hB x').2 ↔
            DeligneDatum.IsPullback (K := K₀) (π := π) B g x.2 x'.2) ∧
        (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] [Algebra 𝒪' B]
            (hB : ∀ x : 𝒪, algebraMap 𝒪 B x = algebraMap 𝒪' B (eb x))
            (B₁ : Type) [CommRing B₁] [Algebra 𝒪 B₁] [Algebra 𝒪' B₁]
            (hB₁ : ∀ x : 𝒪, algebraMap 𝒪 B₁ x = algebraMap 𝒪' B₁ (eb x))
            (f : B →ₐ[𝒪] B₁) (f' : B →ₐ[𝒪'] B₁) (_ : ∀ b, f b = f' b)
            (x : OmegaNrObj (K := K₀) π Onr B) (x₁ : OmegaNrObj (K := K₀) π Onr B₁),
          DeligneDatum.IsBaseChange (K := K₀') (π := π₁) f' (Ψ B hB x).2 (Ψ B₁ hB₁ x₁).2 ↔
            DeligneDatum.IsBaseChange (K := K₀) (π := π) f x.2 x₁.2))

    (hΞ :
      ∃ Ξ : ∀ (B : Type) [CommRing B] [Algebra 𝒪' B], DeligneDatum (K := K₀') π₁ B ≃ DeligneDatum (K := K₀') π' B,
        (∀ (B : Type) [CommRing B] [Algebra 𝒪' B] (d : DeligneDatum (K := K₀') π₁ B), (Ξ B d).line = d.line) ∧
        (∀ (B : Type) [CommRing B] [Algebra 𝒪' B] (g : Matrix.GeneralLinearGroup (Fin 2) K₀')
            (d d' : DeligneDatum (K := K₀') π₁ B),
          DeligneDatum.IsPullback (K := K₀') (π := π') B g (Ξ B d) (Ξ B d') ↔
            DeligneDatum.IsPullback (K := K₀') (π := π₁) B g d d') ∧
        (∀ (B : Type) [CommRing B] [Algebra 𝒪' B] (B' : Type) [CommRing B'] [Algebra 𝒪' B'] (f : B →ₐ[𝒪'] B')
            (d : DeligneDatum (K := K₀') π₁ B) (d' : DeligneDatum (K := K₀') π₁ B'),
          DeligneDatum.IsBaseChange (K := K₀') (π := π') f (Ξ B d) (Ξ B' d') ↔
            DeligneDatum.IsBaseChange (K := K₀') (π := π₁) f d d'))

    (hpkg :
      ∃ (ι : Zp2 r →+* Onr)
        (Φ : FormalODModule r (Onr ⧸ pIdeal r Onr))
        (_ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal r Onr)).comp ι))
        (_ : Φ.HasHeight 4)
        (M : ModuliPackage.{0, 0} r Onr) (_ : M.IsZariskiSheaf)
        (η : ∀ (B : Type) [CommRing B] (ψ : Onr →+* B) (hB : IsNilpotent (r : B)),
          Rigidified r Φ B → M.obj B ψ hB)
        (_ : (∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : Onr →+* B) (hB : IsNilpotent (r : B))
              (t t' : Rigidified r Φ B), t.IsAdmissible ι ψ → t'.IsAdmissible ι ψ →
              (η B ψ hB t = η B ψ hB t' ↔ t.IsIsomorphic t')) ∧
          (∀ (B B' : Type) [CommRing B] [CommRing B'] [IsNoetherianRing B] [IsNoetherianRing B'] (ψ : Onr →+* B) (ψ' : Onr →+* B')
              (hB : IsNilpotent (r : B)) (hB' : IsNilpotent (r : B')) (f : B →+* B')
              (hf : f.comp ψ = ψ') (t : Rigidified r Φ B), t.IsAdmissible ι ψ →
              η B' ψ' hB' (t.map f) = M.map hB hB' f hf (η B ψ hB t)) ∧
          (∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : Onr →+* B) (hB : IsNilpotent (r : B)) (m : M.obj B ψ hB),
              ∃ (n : ℕ) (f : Fin n → B), Ideal.span (Set.range f) = ⊤ ∧
                ∀ (i : Fin n) (L : Type) [CommRing L] [IsNoetherianRing L] [Algebra B L] [IsLocalization.Away (f i) L]
                  (hL : IsNilpotent (r : L)),
                  ∃ t : Rigidified r Φ L, t.IsAdmissible ι ((algebraMap B L).comp ψ) ∧
                    η L ((algebraMap B L).comp ψ) hL t =
                      M.map (ψ' := (algebraMap B L).comp ψ) hB hL (algebraMap B L) rfl m))
        (E₀ : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}) →+* Matrix (Fin 2) (Fin 2) K₀)
        (_ : Function.Injective E₀ ∧
          ∃ m : ℕ,
            (∀ A : Matrix (Fin 2) (Fin 2) 𝒪, ∃ e, E₀ e = (r : K₀) ^ m • A.map (algebraMap 𝒪 K₀)) ∧
            (∀ e, ∃ A : Matrix (Fin 2) (Fin 2) 𝒪, (r : K₀) ^ m • E₀ e = A.map (algebraMap 𝒪 K₀)))
        (e : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → (ModuliPackage.G 𝒪 M).obj B → (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B),

        (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [IsNoetherianRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π))
            (φ : B →ₐ[𝒪] B') (x : (ModuliPackage.G 𝒪 M).obj B), e B' hB' ((ModuliPackage.G 𝒪 M).map φ x) = (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map φ (e B hB x)) ∧

        (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)), Function.Bijective (e B hB)) ∧

        (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (x : (ModuliPackage.G 𝒪 M).obj B), (e B hB x).1 = x.ψ) ∧

        (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (g : Matrix.GeneralLinearGroup (Fin 2) K₀) (x x' : (ModuliPackage.G 𝒪 M).obj B),
            ModuliPackage.G.IsActBy ι Φ η Fr E₀ g x x' ↔ OmegaNr.IsTwistedAct π Onr Fr vdet B g (e B hB x) (e B hB x')) ∧

        (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (x x' : (ModuliPackage.G 𝒪 M).obj B),
            ModuliPackage.G.IsPiTranslate ι Φ η Fr x x' → e B hB x' = (frobTwist Onr Fr 1 (e B hB x).1, (e B hB x).2)) ∧

        (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (x : (ModuliPackage.G 𝒪 M).obj B), ∃ x' : (ModuliPackage.G 𝒪 M).obj B, ModuliPackage.G.IsPiTranslate ι Φ η Fr x x'))
    :
    ∃ (ι : Zp2 r →+* Onr')
      (Φ : FormalODModule r (Onr' ⧸ pIdeal r Onr'))
      (_ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal r Onr')).comp ι))
      (_ : Φ.HasHeight 4)
      (M : ModuliPackage.{0, 0} r Onr') (_ : M.IsZariskiSheaf)
      (η : ∀ (B : Type) [CommRing B] (ψ : Onr' →+* B) (hB : IsNilpotent (r : B)),
        Rigidified r Φ B → M.obj B ψ hB)
      (_ : (∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : Onr' →+* B) (hB : IsNilpotent (r : B))
            (t t' : Rigidified r Φ B), t.IsAdmissible ι ψ → t'.IsAdmissible ι ψ →
            (η B ψ hB t = η B ψ hB t' ↔ t.IsIsomorphic t')) ∧
        (∀ (B B' : Type) [CommRing B] [CommRing B'] [IsNoetherianRing B] [IsNoetherianRing B'] (ψ : Onr' →+* B) (ψ' : Onr' →+* B')
            (hB : IsNilpotent (r : B)) (hB' : IsNilpotent (r : B')) (f : B →+* B')
            (hf : f.comp ψ = ψ') (t : Rigidified r Φ B), t.IsAdmissible ι ψ →
            η B' ψ' hB' (t.map f) = M.map hB hB' f hf (η B ψ hB t)) ∧
        (∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : Onr' →+* B) (hB : IsNilpotent (r : B)) (m : M.obj B ψ hB),
            ∃ (n : ℕ) (f : Fin n → B), Ideal.span (Set.range f) = ⊤ ∧
              ∀ (i : Fin n) (L : Type) [CommRing L] [IsNoetherianRing L] [Algebra B L] [IsLocalization.Away (f i) L]
                (hL : IsNilpotent (r : L)),
                ∃ t : Rigidified r Φ L, t.IsAdmissible ι ((algebraMap B L).comp ψ) ∧
                  η L ((algebraMap B L).comp ψ) hL t =
                    M.map (ψ' := (algebraMap B L).comp ψ) hB hL (algebraMap B L) rfl m))
      (E₀ : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}) →+* Matrix (Fin 2) (Fin 2) K₀')
      (_ : Function.Injective E₀ ∧
        ∃ m : ℕ,
          (∀ A : Matrix (Fin 2) (Fin 2) 𝒪', ∃ e, E₀ e = (r : K₀') ^ m • A.map (algebraMap 𝒪' K₀')) ∧
          (∀ e, ∃ A : Matrix (Fin 2) (Fin 2) 𝒪', (r : K₀') ^ m • E₀ e = A.map (algebraMap 𝒪' K₀')))
      (e : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪' B], IsNilpotent (algebraMap 𝒪' B π') → (ModuliPackage.G 𝒪' M).obj B → (AlgFunctor.prod (AlgFunctor.corep Onr') (Omega K₀' π')).obj B),

      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪' B] (B' : Type) [CommRing B'] [IsNoetherianRing B'] [Algebra 𝒪' B'] (hB : IsNilpotent (algebraMap 𝒪' B π')) (hB' : IsNilpotent (algebraMap 𝒪' B' π'))
          (φ : B →ₐ[𝒪'] B') (x : (ModuliPackage.G 𝒪' M).obj B), e B' hB' ((ModuliPackage.G 𝒪' M).map φ x) = (AlgFunctor.prod (AlgFunctor.corep Onr') (Omega K₀' π')).map φ (e B hB x)) ∧

      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪' B] (hB : IsNilpotent (algebraMap 𝒪' B π')), Function.Bijective (e B hB)) ∧

      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪' B] (hB : IsNilpotent (algebraMap 𝒪' B π')) (x : (ModuliPackage.G 𝒪' M).obj B), (e B hB x).1 = x.ψ) ∧

      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪' B] (hB : IsNilpotent (algebraMap 𝒪' B π')) (g : Matrix.GeneralLinearGroup (Fin 2) K₀') (x x' : (ModuliPackage.G 𝒪' M).obj B),
          ModuliPackage.G.IsActBy ι Φ η Fr' E₀ g x x' ↔ OmegaNr.IsTwistedAct π' Onr' Fr' vdet' B g (e B hB x) (e B hB x')) ∧

      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪' B] (hB : IsNilpotent (algebraMap 𝒪' B π')) (x x' : (ModuliPackage.G 𝒪' M).obj B),
          ModuliPackage.G.IsPiTranslate ι Φ η Fr' x x' → e B hB x' = (frobTwist Onr' Fr' 1 (e B hB x).1, (e B hB x).2)) ∧

      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪' B] (x : (ModuliPackage.G 𝒪' M).obj B), ∃ x' : (ModuliPackage.G 𝒪' M).obj B, ModuliPackage.G.IsPiTranslate ι Φ η Fr' x x') := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_exists_G_bijective_isActBy_iff_isTwistedAct_of_ringEquiv_frame_of_isNoetherianRing.solution
