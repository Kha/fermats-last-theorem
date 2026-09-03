import Mathlib
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSum
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_prodKerGraph_comap_fst_eq_prodKerGraph_comap_of_isPullback

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry~prodKerGraph_comap_mapOnProdOver"

theorem AlgebraicGeometry.prodKerGraph_comap_fst_eq_prodKerGraph_comap_of_isPullback
    {𝒞 𝒞' S S' : Scheme.{u}} (f : 𝒞 ⟶ S) (f' : 𝒞' ⟶ S') [IsSeparated f] [IsSeparated f']
    (h : S' ⟶ S) (g' : 𝒞' ⟶ 𝒞) (H : IsPullback g' f' f h)
    {r : ℕ} (a : Fin r → (S ⟶ 𝒞)) (ha : ∀ i, a i ≫ f = 𝟙 S)
    (b : Fin r → (S' ⟶ 𝒞')) (hb : ∀ i, b i ≫ f' = 𝟙 S')
    (hab : ∀ i, b i ≫ g' = h ≫ a i)
    (θ : pullback (pullback.snd f (𝟙 S)) h ⟶ pullback f' (𝟙 S'))
    (hθ₁ : θ ≫ pullback.fst f' (𝟙 S') ≫ g' = pullback.fst (pullback.snd f (𝟙 S)) h ≫ pullback.fst f (𝟙 S))
    (hθ₂ : θ ≫ pullback.snd f' (𝟙 S') = pullback.snd (pullback.snd f (𝟙 S)) h) :
    (prodKerGraph f a ha).comap (pullback.fst (pullback.snd f (𝟙 S)) h) =
      (prodKerGraph f' b hb).comap θ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_prodKerGraph_comap_fst_eq_prodKerGraph_comap_of_isPullback.solution
