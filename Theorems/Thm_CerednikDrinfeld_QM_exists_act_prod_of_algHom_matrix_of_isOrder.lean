import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawProd
import Definitions.Def_QuaternionAlgebra_Order
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_exists_act_prod_of_algHom_matrix_of_isOrder

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra
  CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

theorem CerednikDrinfeld.QM.exists_act_prod_of_algHom_matrix_of_isOrder
    {R : Type} [CommRing R]
    {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of R)) (L : RelativeGroupLaw R f) (hLc : L.IsCommutative)
    {c d : ℚ} (O : Submodule ℤ ℍ[ℚ, c, d]) (hO : IsOrder O)
    (ε : ↥O → (A ⟶ A)) (hε : ∀ x : ↥O, ε x ≫ f = f)
    (hε_hom : ∀ (x : ↥O) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      pushPt (ε x) (hε x) (L.mul t P Q) = L.mul t (pushPt (ε x) (hε x) P) (pushPt (ε x) (hε x) Q))
    (hε_one : ∀ h : (1 : ℍ[ℚ, c, d]) ∈ O, ε ⟨1, h⟩ = 𝟙 A)
    (hε_mul : ∀ (x y : ↥O) (h : (x : ℍ[ℚ, c, d]) * (y : ℍ[ℚ, c, d]) ∈ O),
      ε ⟨(x : ℍ[ℚ, c, d]) * (y : ℍ[ℚ, c, d]), h⟩ = ε y ≫ ε x)
    (hε_add : ∀ (x y : ↥O) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (P : SchemeHomOver t f),
      pushPt (ε (x + y)) (hε (x + y)) P = L.mul t (pushPt (ε x) (hε x) P) (pushPt (ε y) (hε y) P))
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b])
    (j : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d])
    (hj : ∀ (m : ↥Λ) (i l : Fin 2), j (m : ℍ[ℚ, a, b]) i l ∈ O) :
    ∃ (act : ↥Λ → (pullback f f ⟶ pullback f f)) (hact : ∀ m : ↥Λ, act m ≫ prodStr f f = prodStr f f),
      (∀ (m : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (P : SchemeHomOver t (prodStr f f)),
        prodFstPt (pushPt (act m) (hact m) P) =
            L.mul t (pushPt (ε ⟨j (m : ℍ[ℚ, a, b]) 0 0, hj m 0 0⟩) (hε _) (prodFstPt P))
              (pushPt (ε ⟨j (m : ℍ[ℚ, a, b]) 0 1, hj m 0 1⟩) (hε _) (prodSndPt P)) ∧
          prodSndPt (pushPt (act m) (hact m) P) =
            L.mul t (pushPt (ε ⟨j (m : ℍ[ℚ, a, b]) 1 0, hj m 1 0⟩) (hε _) (prodFstPt P))
              (pushPt (ε ⟨j (m : ℍ[ℚ, a, b]) 1 1, hj m 1 1⟩) (hε _) (prodSndPt P))) ∧
      (∀ (m : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t (prodStr f f)),
        pushPt (act m) (hact m) ((L.prod L).mul t P Q) =
          (L.prod L).mul t (pushPt (act m) (hact m) P) (pushPt (act m) (hact m) Q)) ∧
      (∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, act ⟨1, h⟩ = 𝟙 (pullback f f)) ∧
      (∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
        act ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = act y ≫ act x) ∧
      (∀ (x y : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (P : SchemeHomOver t (prodStr f f)),
        pushPt (act (x + y)) (hact (x + y)) P =
          (L.prod L).mul t (pushPt (act x) (hact x) P) (pushPt (act y) (hact y) P)) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_exists_act_prod_of_algHom_matrix_of_isOrder.solution
