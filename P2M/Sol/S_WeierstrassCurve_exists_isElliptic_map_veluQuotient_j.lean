import Definitions.Def_WeierstrassCurve_VeluQuotientMap
import Theorems.Thm_WeierstrassCurve_map_veluQuotient_image
import P2M.Util
namespace P2MW.S_WeierstrassCurve_exists_isElliptic_map_veluQuotient_j

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "map map_j map_a₁ j map_a₃ IsOddVeluSet veluGy veluQuotient map_veluQuotient_image"
p2m_open "WeierstrassCurve"

private theorem exists_isElliptic_map_veluQuotient_j {R R' : Type*} [Field R] [Field R']
    [DecidableEq R'] (W : WeierstrassCurve R) (f : R →+* R') (S : Finset (R × R))
    (hQ : (W.veluQuotient S).IsElliptic) :
    ∃ hQ' : ((W.map f).veluQuotient (S.image (Prod.map f f))).IsElliptic,
      @WeierstrassCurve.j R' _ ((W.map f).veluQuotient (S.image (Prod.map f f))) hQ' =
        f (@WeierstrassCurve.j R _ (W.veluQuotient S) hQ) := by
  have hinj : (S.image (Prod.map f f)).card = S.card :=
    Finset.card_image_of_injective S (f.injective.prodMap f.injective)
  have hmap : (W.map f).veluQuotient (S.image (Prod.map f f)) = (W.veluQuotient S).map f :=
    WeierstrassCurve.map_veluQuotient_image W f S hinj
  have key : ∀ (V : WeierstrassCurve R'), V = (W.veluQuotient S).map f →
      ∃ hV : V.IsElliptic, @WeierstrassCurve.j R' _ V hV =
        f (@WeierstrassCurve.j R _ (W.veluQuotient S) hQ) := by
    rintro V rfl
    exact ⟨inferInstance, (W.veluQuotient S).map_j f⟩
  exact key _ hmap

namespace IsOddVeluSet p2m_export "WeierstrassCurve.IsOddVeluSet" "gy_ne_zero equation x_injOn" end IsOddVeluSet
namespace IsOddVeluSet
p2m_open_scoped "WeierstrassCurve.IsOddVeluSet" in

private theorem _root_.WeierstrassCurve.IsOddVeluSet.image {R R' : Type*} [CommRing R] [CommRing R'] [DecidableEq R']
    {W : WeierstrassCurve R} {S : Finset (R × R)} (h : W.IsOddVeluSet S) (f : R →+* R')
    (hf : Function.Injective f) : (W.map f).IsOddVeluSet (S.image (Prod.map f f)) := by
  have hgy : ∀ x y : R, (W.map f).veluGy (f x) (f y) = f (W.veluGy x y) := by
    intro x y
    simp only [veluGy, map_a₁, map_a₃, map_neg, map_add, map_mul, map_ofNat]
  refine ⟨?_, ?_, ?_⟩
  · intro P hP
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hP
    exact (h.equation Q hQ).map f
  · intro P hP
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hP
    show (W.map f).veluGy (f Q.1) (f Q.2) ≠ 0
    rw [hgy, map_ne_zero_iff f hf]
    exact h.gy_ne_zero Q hQ
  · intro P hP P' hP' hx
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hP
    obtain ⟨Q', hQ', rfl⟩ := Finset.mem_image.mp hP'
    have hQQ' : Q = Q' := h.x_injOn Q hQ Q' hQ' (hf hx)
    rw [hQQ']

end IsOddVeluSet
p2m_export "WeierstrassCurve" "IsOddVeluSet.image"
end WeierstrassCurve

theorem solution {R R' : Type*} [Field R] [Field R']
    [DecidableEq R'] (W : WeierstrassCurve R) (f : R →+* R') (S : Finset (R × R))
    (hQ : (W.veluQuotient S).IsElliptic) :
    ∃ hQ' : ((W.map f).veluQuotient (S.image (Prod.map f f))).IsElliptic,
      @WeierstrassCurve.j R' _ ((W.map f).veluQuotient (S.image (Prod.map f f))) hQ' =
        f (@WeierstrassCurve.j R _ (W.veluQuotient S) hQ) :=
  WeierstrassCurve.exists_isElliptic_map_veluQuotient_j W f S hQ

