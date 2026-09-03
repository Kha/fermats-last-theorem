import Mathlib
import P2M.Util
import P2M.Sol.S_HomogeneousLocalization_Away_isPushout_map_of_isBaseChange

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomogeneousLocalization

theorem HomogeneousLocalization.Away.isPushout_map_of_isBaseChange
    {S : Type u} [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S']
    (R : Type u) [CommRing R] [Algebra S R] (𝓡 : ℕ → Submodule S R) [GradedAlgebra 𝓡]
    (R' : Type u) [CommRing R'] [Algebra S' R'] [Algebra S R'] [IsScalarTower S S' R']
    (𝓡' : ℕ → Submodule S' R') [GradedAlgebra 𝓡']
    (ϑ : R →ₐ[S] R') (hϑdeg : ∀ n, ∀ x ∈ 𝓡 n, ϑ x ∈ 𝓡' n)
    (hbc : ∀ n, IsBaseChange S' ((ϑ.toLinearMap.restrict (p := 𝓡 n) (q := (𝓡' n).restrictScalars S) (hϑdeg n))
      : 𝓡 n →ₗ[S] (𝓡' n).restrictScalars S))
    {d : ℕ} (r : R) (hr : r ∈ 𝓡 d) :
    IsPushout
      (CommRingCat.ofHom ((HomogeneousLocalization.fromZeroRingHom 𝓡 (Submonoid.powers r)).comp
        ((GradedRing.projZeroRingHom' 𝓡).comp (algebraMap S R))))
      (CommRingCat.ofHom (algebraMap S S'))
      (CommRingCat.ofHom (HomogeneousLocalization.Away.map ({ ϑ.toRingHom with map_mem := fun h => hϑdeg _ _ h } : 𝓡 →+*ᵍ 𝓡') r))
      (CommRingCat.ofHom ((HomogeneousLocalization.fromZeroRingHom 𝓡'
          (Submonoid.powers (({ ϑ.toRingHom with map_mem := fun h => hϑdeg _ _ h } : 𝓡 →+*ᵍ 𝓡') r))).comp
        ((GradedRing.projZeroRingHom' 𝓡').comp (algebraMap S' R')))) := by p2m_exact_reverting @_root_.P2MW.S_HomogeneousLocalization_Away_isPushout_map_of_isBaseChange.solution
