import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalOmega_AlgFunctor_formalQuotient_descent

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.AlgFunctor.formalQuotient_descent
    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (F : AlgFunctor 𝒪)

    (Γ : Type) [Group Γ] (act : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], Γ → F.obj B → F.obj B → Prop)
    (hact_fun : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (γ : Γ) (x x' x'' : F.obj B), act B γ x x' → act B γ x x'' → x' = x'')
    (hact_total : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (γ : Γ) (x : F.obj B), ∃ x', act B γ x x')
    (hact_one : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (x : F.obj B), act B 1 x x)
    (hact_mul : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (γ γ' : Γ) (x y z : F.obj B), act B γ x y → act B γ' y z → act B (γ' * γ) x z)
    (hact_nat : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (φ : B →ₐ[𝒪] B') (γ : Γ)
      (x x' : F.obj B), act B γ x x' → act B' γ (F.map φ x) (F.map φ x'))
    (Γ' : Subgroup Γ)

    (𝒳' 𝒳 : Scheme.{0}) (f' : 𝒳' ⟶ Spec (CommRingCat.of 𝒪)) (f : 𝒳 ⟶ Spec (CommRingCat.of 𝒪))
    (p : 𝒳' ⟶ 𝒳) (hp : p ≫ f = f')
    (a : Γ → (𝒳' ⟶ 𝒳')) (ha_over : ∀ γ, a γ ≫ f' = f') (ha_p : ∀ γ, a γ ≫ p = p) (ha_one : ∀ γ ∈ Γ', a γ = 𝟙 𝒳')
    (ha_mul : ∀ γ γ' : Γ, a (γ' * γ) = a γ ≫ a γ')

    (hp_univ : ∀ (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of 𝒪)) (ρ : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → (Scheme.nilpPoints f').obj B → (Scheme.nilpPoints t).obj B),
      (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π))
        (φ : B →ₐ[𝒪] B') (x : (Scheme.nilpPoints f').obj B), ρ B' hB' ((Scheme.nilpPoints f').map φ x) = (Scheme.nilpPoints t).map φ (ρ B hB x)) →
      (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (γ : Γ) (y : (Scheme.nilpPoints f').obj B),
        ρ B hB ((Scheme.nilpPoints.mapHom f' f' (a γ) (ha_over γ)).app B y) = ρ B hB y) →
      ∃ u : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → (Scheme.nilpPoints f).obj B → (Scheme.nilpPoints t).obj B,
        (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π))
        (φ : B →ₐ[𝒪] B') (x : (Scheme.nilpPoints f).obj B), u B' hB' ((Scheme.nilpPoints f).map φ x) = (Scheme.nilpPoints t).map φ (u B hB x)) ∧
        (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (y : (Scheme.nilpPoints f').obj B),
          u B hB ((Scheme.nilpPoints.mapHom f' f p hp).app B y) = ρ B hB y) ∧
        ∀ u' : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → (Scheme.nilpPoints f).obj B → (Scheme.nilpPoints t).obj B, (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π))
        (φ : B →ₐ[𝒪] B') (x : (Scheme.nilpPoints f).obj B), u' B' hB' ((Scheme.nilpPoints f).map φ x) = (Scheme.nilpPoints t).map φ (u' B hB x)) →
          (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (y : (Scheme.nilpPoints f').obj B),
            u' B hB ((Scheme.nilpPoints.mapHom f' f p hp).app B y) = ρ B hB y) →
          ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (z : (Scheme.nilpPoints f).obj B), u' B hB z = u B hB z)

    (Θ' : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → F.obj B → (Scheme.nilpPoints f').obj B)
    (hΘ'_nat : (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π))
        (φ : B →ₐ[𝒪] B') (x : F.obj B), Θ' B' hB' (F.map φ x) = (Scheme.nilpPoints f').map φ (Θ' B hB x)))
    (hΘ'_eqv : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (γ : Γ) (x x' : F.obj B), act B γ x x' →
      Θ' B hB x' = (Scheme.nilpPoints.mapHom f' f' (a γ) (ha_over γ)).app B (Θ' B hB x))
    (hΘ'_univ : ∀ (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of 𝒪)) (ρ : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → F.obj B → (Scheme.nilpPoints t).obj B),
      (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π))
        (φ : B →ₐ[𝒪] B') (x : F.obj B), ρ B' hB' (F.map φ x) = (Scheme.nilpPoints t).map φ (ρ B hB x)) →
      (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (γ : Γ), γ ∈ Γ' → ∀ x x' : F.obj B, act B γ x x' → ρ B hB x' = ρ B hB x) →
      ∃ u : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → (Scheme.nilpPoints f').obj B → (Scheme.nilpPoints t).obj B,
        (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π))
        (φ : B →ₐ[𝒪] B') (x : (Scheme.nilpPoints f').obj B), u B' hB' ((Scheme.nilpPoints f').map φ x) = (Scheme.nilpPoints t).map φ (u B hB x)) ∧
        (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (x : F.obj B), u B hB (Θ' B hB x) = ρ B hB x) ∧
        ∀ u' : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → (Scheme.nilpPoints f').obj B → (Scheme.nilpPoints t).obj B, (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π))
        (φ : B →ₐ[𝒪] B') (x : (Scheme.nilpPoints f').obj B), u' B' hB' ((Scheme.nilpPoints f').map φ x) = (Scheme.nilpPoints t).map φ (u' B hB x)) →
          (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (x : F.obj B), u' B hB (Θ' B hB x) = ρ B hB x) →
          ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (y : (Scheme.nilpPoints f').obj B), u' B hB y = u B hB y)
    :

    let Θ : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → F.obj B → (Scheme.nilpPoints f).obj B := fun B _ _ hB x => (Scheme.nilpPoints.mapHom f' f p hp).app B (Θ' B hB x)
    (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π))
        (φ : B →ₐ[𝒪] B') (x : F.obj B), Θ B' hB' (F.map φ x) = (Scheme.nilpPoints f).map φ (Θ B hB x)) ∧
    (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (γ : Γ) (x x' : F.obj B), act B γ x x' → Θ B hB x' = Θ B hB x) ∧
    (∀ (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of 𝒪)) (ρ : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → F.obj B → (Scheme.nilpPoints t).obj B),
      (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π))
        (φ : B →ₐ[𝒪] B') (x : F.obj B), ρ B' hB' (F.map φ x) = (Scheme.nilpPoints t).map φ (ρ B hB x)) →
      (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (γ : Γ) (x x' : F.obj B), act B γ x x' → ρ B hB x' = ρ B hB x) →
      ∃ u : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → (Scheme.nilpPoints f).obj B → (Scheme.nilpPoints t).obj B,
        (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π))
        (φ : B →ₐ[𝒪] B') (x : (Scheme.nilpPoints f).obj B), u B' hB' ((Scheme.nilpPoints f).map φ x) = (Scheme.nilpPoints t).map φ (u B hB x)) ∧
        (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (x : F.obj B), u B hB (Θ B hB x) = ρ B hB x) ∧
        ∀ u' : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → (Scheme.nilpPoints f).obj B → (Scheme.nilpPoints t).obj B, (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π))
        (φ : B →ₐ[𝒪] B') (x : (Scheme.nilpPoints f).obj B), u' B' hB' ((Scheme.nilpPoints f).map φ x) = (Scheme.nilpPoints t).map φ (u' B hB x)) →
          (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (x : F.obj B), u' B hB (Θ B hB x) = ρ B hB x) →
          ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (z : (Scheme.nilpPoints f).obj B), u' B hB z = u B hB z) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalOmega_AlgFunctor_formalQuotient_descent.solution
