import Mathlib
import Definitions.Def_MvFormalGroup_BasicV2
import Definitions.Def_MvFormalGroup_PointsV2
import P2M.Util
import P2M.Sol.S_MvFormalGroup_existsUnique_isComm_and_apply_eq_adicEval_toPowerSeries_of_natural

universe u

theorem MvFormalGroup.existsUnique_isComm_and_apply_eq_adicEval_toPowerSeries_of_natural
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞] (d : ℕ)
    (μ : ∀ (g : Type u) [CommRing g] [Algebra 𝓞 g], (Fin d → g) → (Fin d → g) → (Fin d → g))
    (hμ_mem : ∀ (g : Type u) [CommRing g] [Algebra 𝓞 g] [Module.Free 𝓞 g] [Module.Finite 𝓞 g]
      (x y : Fin d → g), (∀ j, x j ∈ (Ideal.span {(p : g)}).radical) → (∀ j, y j ∈ (Ideal.span {(p : g)}).radical) →
      ∀ j, μ g x y j ∈ (Ideal.span {(p : g)}).radical)
    (hμ_zero : ∀ (g : Type u) [CommRing g] [Algebra 𝓞 g] [Module.Free 𝓞 g] [Module.Finite 𝓞 g]
      (x : Fin d → g), (∀ j, x j ∈ (Ideal.span {(p : g)}).radical) → μ g x 0 = x ∧ μ g 0 x = x)
    (hμ_assoc : ∀ (g : Type u) [CommRing g] [Algebra 𝓞 g] [Module.Free 𝓞 g] [Module.Finite 𝓞 g]
      (x y z : Fin d → g), (∀ j, x j ∈ (Ideal.span {(p : g)}).radical) → (∀ j, y j ∈ (Ideal.span {(p : g)}).radical) →
      (∀ j, z j ∈ (Ideal.span {(p : g)}).radical) → μ g (μ g x y) z = μ g x (μ g y z))
    (hμ_comm : ∀ (g : Type u) [CommRing g] [Algebra 𝓞 g] [Module.Free 𝓞 g] [Module.Finite 𝓞 g]
      (x y : Fin d → g), (∀ j, x j ∈ (Ideal.span {(p : g)}).radical) → (∀ j, y j ∈ (Ideal.span {(p : g)}).radical) → μ g x y = μ g y x)
    (hμ_nat : ∀ (g g' : Type u) [CommRing g] [Algebra 𝓞 g] [Module.Free 𝓞 g] [Module.Finite 𝓞 g]
      [CommRing g'] [Algebra 𝓞 g'] [Module.Free 𝓞 g'] [Module.Finite 𝓞 g']
      (φ : g →ₐ[𝓞] g') (x y : Fin d → g), (∀ j, x j ∈ (Ideal.span {(p : g)}).radical) → (∀ j, y j ∈ (Ideal.span {(p : g)}).radical) →
      μ g' (φ ∘ x) (φ ∘ y) = φ ∘ μ g x y) :
    ∃! Φ : MvFormalGroup d 𝓞, Φ.IsComm ∧
      ∀ (g : Type u) [CommRing g] [Algebra 𝓞 g] [Module.Free 𝓞 g] [Module.Finite 𝓞 g]
        (x y : Fin d → g), (∀ j, IsNilpotent (x j)) → (∀ j, IsNilpotent (y j)) →
        ∀ i, μ g x y i =
          MvFormalGroup.adicEval (Ideal.span {(p : g)}) (Sum.elim x y) (Φ.toPowerSeries i) := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_existsUnique_isComm_and_apply_eq_adicEval_toPowerSeries_of_natural.solution
