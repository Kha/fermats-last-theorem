import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalOmega_Omega_bijective_of_algFunctor_of_forall_existsUnique_lift_of_forall_bijective_of_forall_represents_inEdgeChart
attribute [-instance] CerednikDrinfeld.FormalOmega.edgeQuot.instCommRing CerednikDrinfeld.FormalOmega.edgeQuot.instAlgebra CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₀

set_option autoImplicit false

open scoped TensorProduct
open CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.Omega.bijective_of_algFunctor_of_forall_existsUnique_lift_of_forall_bijective_of_forall_represents_inEdgeChart

    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K₀ : Type} [Field K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]
    (π : 𝒪) (hπ : Irreducible π) (q : ℕ) (hq : Nat.card (𝒪 ⧸ Ideal.span {π}) = q) [Finite (𝒪 ⧸ Ideal.span {π})]

    (C : Type) [CommRing C] [IsNoetherianRing C] [Algebra 𝒪 C] (hC : IsNilpotent (algebraMap 𝒪 C π))

    (PR : AlgFunctor C)
    (hsheaf : ∀ (A : Type) [CommRing A] [Algebra C A] (n : ℕ) (f : Fin n → A),
      Ideal.span (Set.range f) = ⊤ →
      ∀ (B : Fin n → Type) [∀ i, CommRing (B i)] [∀ i, Algebra A (B i)] [∀ i, Algebra C (B i)]
        [∀ i, IsScalarTower C A (B i)] [∀ i, IsLocalization.Away (f i) (B i)] (s : ∀ i, PR.obj (B i)),
      (∀ (i j : Fin n) (D : Type) [CommRing D] [Algebra A D] [Algebra C D] [IsScalarTower C A D]
          [IsLocalization.Away (f i * f j) D] (ρ₁ : B i →ₐ[A] D) (ρ₂ : B j →ₐ[A] D),
          PR.map (ρ₁.restrictScalars C) (s i) = PR.map (ρ₂.restrictScalars C) (s j)) →
      ∃! s₀ : PR.obj A, ∀ i, PR.map (IsScalarTower.toAlgHom C A (B i)) s₀ = s i)

    (θ : ∀ (S : Type) [CommRing S] [Algebra C S] [IsNoetherianRing S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S],
      PR.obj S → (Omega K₀ π).obj S)
    (hnat : ∀ (S S' : Type) [CommRing S] [Algebra C S] [IsNoetherianRing S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
      [CommRing S'] [Algebra C S'] [IsNoetherianRing S'] [Algebra 𝒪 S'] [IsScalarTower 𝒪 C S']
      (φ : S →ₐ[C] S') (x : PR.obj S),
      θ S' (PR.map φ x) = (Omega K₀ π).map (φ.restrictScalars 𝒪) (θ S x))

    (het : ∀ (S S₀ : Type) [CommRing S] [IsLocalRing S] [IsArtinianRing S] [IsAlgClosed (IsLocalRing.ResidueField S)]
      [Algebra C S] [IsNoetherianRing S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
      [CommRing S₀] [Nontrivial S₀] [Algebra C S₀] [IsNoetherianRing S₀] [Algebra 𝒪 S₀] [IsScalarTower 𝒪 C S₀]
      (p : S →ₐ[C] S₀), Function.Surjective p → (∀ s t : S, p s = 0 → p t = 0 → s * t = 0) →
      ∀ (x₀ : PR.obj S₀) (d : (Omega K₀ π).obj S),
        θ S₀ x₀ = (Omega K₀ π).map (p.restrictScalars 𝒪) d →
        ∃! x : PR.obj S, PR.map p x = x₀ ∧ θ S x = d)

    (hpts : ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra C k] [Algebra 𝒪 k] [IsScalarTower 𝒪 C k],
      Function.Bijective (θ k))

    (g : Matrix.GeneralLinearGroup (Fin 2) K₀) (hg : (g : Matrix (Fin 2) (Fin 2) K₀) = Matrix.diagonal ![algebraMap 𝒪 K₀ π, 1])

    (hrep : ∀ γ : Matrix.GeneralLinearGroup (Fin 2) K₀,
      ∃ (X : Scheme.{0}) (fX : X ⟶ Spec (CommRingCat.of C)) (_ : LocallyOfFiniteType fX)
        (e : ∀ (S : Type) [CommRing S] [Algebra C S] [IsNoetherianRing S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S],
          (Scheme.nilpPoints fX).obj S → PR.obj S),

        (∀ (S S' : Type) [CommRing S] [Algebra C S] [IsNoetherianRing S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
            [CommRing S'] [Algebra C S'] [IsNoetherianRing S'] [Algebra 𝒪 S'] [IsScalarTower 𝒪 C S'] (φ : S →ₐ[C] S')
            (y : (Scheme.nilpPoints fX).obj S)
            (y' : (Scheme.nilpPoints fX).obj S'),
            y'.1 = Spec.map (CommRingCat.ofHom (φ : S →+* S')) ≫ y.1 → e S' y' = PR.map φ (e S y)) ∧

        (∀ (S : Type) [CommRing S] [Algebra C S] [IsNoetherianRing S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
            (y y' : (Scheme.nilpPoints fX).obj S), e S y = e S y' → y = y') ∧

        (∀ (S : Type) [CommRing S] [Algebra C S] [IsNoetherianRing S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S] (x : PR.obj S),
            (∃ y : (Scheme.nilpPoints fX).obj S, e S y = x) ↔
              DeligneDatum.InEdgeChart π (θ S x) (FullLattice.act γ (FullLattice.act g (stdFullLattice K₀)))
                (FullLattice.act γ (stdFullLattice K₀)))) :
    ∀ (S : Type) [CommRing S] [Algebra C S] [IsNoetherianRing S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S],
      Function.Bijective (θ S) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalOmega_Omega_bijective_of_algFunctor_of_forall_existsUnique_lift_of_forall_bijective_of_forall_represents_inEdgeChart.solution
