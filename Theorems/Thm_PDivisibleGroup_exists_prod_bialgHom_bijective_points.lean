import Mathlib
import Definitions.Def_PDivisibleGroup_Points
import P2M.Util
import P2M.Sol.S_PDivisibleGroup_exists_prod_bialgHom_bijective_points

set_option autoImplicit false

theorem PDivisibleGroup.exists_prod_bialgHom_bijective_points
    {R : Type} [CommRing R] {p h h' : ℕ} [Fact p.Prime] (G : PDivisibleGroup R p h) (H : PDivisibleGroup R p h') :
    ∃ (P : PDivisibleGroup R p (h + h'))
      (iG : ∀ v : ℕ, G.level v →ₐc[R] P.level v) (iH : ∀ v : ℕ, H.level v →ₐc[R] P.level v),
      (∀ v : ℕ, (iG v).comp (G.transition v) = (P.transition v).comp (iG (v + 1))) ∧
      (∀ v : ℕ, (iH v).comp (H.transition v) = (P.transition v).comp (iH (v + 1))) ∧
      ∀ (L : Type) [CommRing L] [Algebra R L] (v : ℕ),
        Function.Bijective (fun x : P.Point L v =>
          ((PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom x).comp (iG v : G.level v →ₐ[R] P.level v)) :
              G.Point L v),
           (PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom x).comp (iH v : H.level v →ₐ[R] P.level v)) :
              H.Point L v))) ∧
        ∀ x y : P.Point L v,
          (PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom (x * y)).comp (iG v : G.level v →ₐ[R] P.level v)) :
              G.Point L v) =
            PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom x).comp (iG v : G.level v →ₐ[R] P.level v)) *
              PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom y).comp (iG v : G.level v →ₐ[R] P.level v)) ∧
          (PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom (x * y)).comp (iH v : H.level v →ₐ[R] P.level v)) :
              H.Point L v) =
            PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom x).comp (iH v : H.level v →ₐ[R] P.level v)) *
              PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom y).comp (iH v : H.level v →ₐ[R] P.level v)) := by p2m_exact_reverting @_root_.P2MW.S_PDivisibleGroup_exists_prod_bialgHom_bijective_points.solution
