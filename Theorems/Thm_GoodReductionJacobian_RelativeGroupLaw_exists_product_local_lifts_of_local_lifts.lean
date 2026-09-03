import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_product_local_lifts_of_local_lifts

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing Scheme.TwoAffineOpenCover

universe u
theorem GoodReductionJacobian.RelativeGroupLaw.exists_product_local_lifts_of_local_lifts
    (T' T : Type u) [CommRing T'] [IsLocalRing T'] [IsArtinianRing T']
    [CommRing T] (π : T' →+* T) (hπ : Function.Surjective π) (hker : IsNilpotent (RingHom.ker π))
    {A₀ : Scheme.{u}} (f₀ : A₀ ⟶ Spec (CommRingCat.of T)) [IsSeparated f₀] [Smooth f₀]
    (L₀ : RelativeGroupLaw T f₀)
    (ρ : T →+* ResidueField T') (hρ : ρ.comp π = residue T')

    (𝒰 : A₀.OrderedAffineCover)
    (Y : 𝒰.ι → Scheme.{u}) (q : ∀ a, Y a ⟶ Spec (CommRingCat.of T')) (hq : ∀ a, Smooth (q a))
    (g : ∀ a, (↑(𝒰.U a) : Scheme.{u}) ⟶ Y a)
    (hg : ∀ a, IsPullback (g a) ((𝒰.U a).ι ≫ f₀) (q a) (Spec.map (CommRingCat.ofHom π)))

    {Ak : Scheme.{u}} (fk : Ak ⟶ Spec (CommRingCat.of (ResidueField T'))) [IsSeparated fk]
    (Lk : RelativeGroupLaw (ResidueField T') fk)
    (i₀ : Ak ⟶ A₀) [IsAffineHom i₀] (hi₀ : IsPullback i₀ fk f₀ (Spec.map (CommRingCat.ofHom ρ)))
    (hLk : ∀ {S : Scheme.{u}} (t : S ⟶ Spec (CommRingCat.of (ResidueField T'))) (P Q : SchemeHomOver t fk),
      (Lk.mul t P Q).1 ≫ i₀ =
        (L₀.mul (t ≫ Spec.map (CommRingCat.ofHom ρ))
          ⟨P.1 ≫ i₀, by rw [Category.assoc, hi₀.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ i₀, by rw [Category.assoc, hi₀.w, ← Category.assoc, Q.2]⟩).1)
    (𝒲 : (pullback fk fk).OrderedAffineCover) (lam₁ lam₂ lam₃ : 𝒲.ι → 𝒰.ι)
    (h₁ : ∀ w, 𝒲.U w ≤ pullback.fst fk fk ⁻¹ᵁ (𝒰.comap i₀).U (lam₁ w))
    (h₂ : ∀ w, 𝒲.U w ≤ pullback.snd fk fk ⁻¹ᵁ (𝒰.comap i₀).U (lam₂ w))
    (h₃ : ∀ w, 𝒲.U w ≤ (Lk.mul (pullback.fst fk fk ≫ fk) ⟨pullback.fst fk fk, rfl⟩ ⟨pullback.snd fk fk, pullback.condition.symm⟩).1 ⁻¹ᵁ (𝒰.comap i₀).U (lam₃ w)) :
    ∃
      (_ : IsAffineHom (pullback.lift (pullback.fst fk fk ≫ i₀) (pullback.snd fk fk ≫ i₀)
          (by rw [Category.assoc, Category.assoc, hi₀.w, ← Category.assoc, ← Category.assoc, pullback.condition])))
      (_ : IsPullback (pullback.lift (pullback.fst fk fk ≫ i₀) (pullback.snd fk fk ≫ i₀)
          (by rw [Category.assoc, Category.assoc, hi₀.w, ← Category.assoc, ← Category.assoc, pullback.condition]))
            (pullback.fst fk fk ≫ fk) (pullback.fst f₀ f₀ ≫ f₀) (Spec.map (CommRingCat.ofHom ρ)))

      (Vop : 𝒲.ι → (pullback f₀ f₀).Opens) (_ : ∀ w, IsAffineOpen (Vop w)) (_ : ⨆ w, Vop w = ⊤)
      (_ : ∀ w, (pullback.lift (pullback.fst fk fk ≫ i₀) (pullback.snd fk fk ≫ i₀)
          (by rw [Category.assoc, Category.assoc, hi₀.w, ← Category.assoc, ← Category.assoc, pullback.condition])) ⁻¹ᵁ (Vop w) = 𝒲.U w)
      (hV₁ : ∀ w, Vop w ≤ pullback.fst f₀ f₀ ⁻¹ᵁ 𝒰.U (lam₁ w))
      (hV₂ : ∀ w, Vop w ≤ pullback.snd f₀ f₀ ⁻¹ᵁ 𝒰.U (lam₂ w))
      (hV₃ : ∀ w, Vop w ≤ (L₀.mul (pullback.fst f₀ f₀ ≫ f₀) ⟨pullback.fst f₀ f₀, rfl⟩ ⟨pullback.snd f₀ f₀, pullback.condition.symm⟩).1 ⁻¹ᵁ 𝒰.U (lam₃ w))

      (Z : 𝒲.ι → Scheme.{u}) (qZ : ∀ w, Z w ⟶ Spec (CommRingCat.of T')) (_ : ∀ w, IsAffine (Z w)) (_ : ∀ w, Smooth (qZ w))
      (gZ : ∀ w, (↑(Vop w) : Scheme.{u}) ⟶ Z w)
      (_ : ∀ w, IsPullback (gZ w) ((Vop w).ι ≫ pullback.fst f₀ f₀ ≫ f₀) (qZ w) (Spec.map (CommRingCat.ofHom π)))

      (hZ₁ : ∀ w, Z w ⟶ Y (lam₁ w)) (hZ₂ : ∀ w, Z w ⟶ Y (lam₂ w)) (hZ₃ : ∀ w, Z w ⟶ Y (lam₃ w)),
      (∀ w, hZ₁ w ≫ q (lam₁ w) = qZ w ∧ gZ w ≫ hZ₁ w = (pullback f₀ f₀).homOfLE (hV₁ w) ≫ (pullback.fst f₀ f₀ ∣_ 𝒰.U (lam₁ w)) ≫ g (lam₁ w)) ∧
      (∀ w, hZ₂ w ≫ q (lam₂ w) = qZ w ∧ gZ w ≫ hZ₂ w = (pullback f₀ f₀).homOfLE (hV₂ w) ≫ (pullback.snd f₀ f₀ ∣_ 𝒰.U (lam₂ w)) ≫ g (lam₂ w)) ∧
      (∀ w, hZ₃ w ≫ q (lam₃ w) = qZ w ∧
        gZ w ≫ hZ₃ w = (pullback f₀ f₀).homOfLE (hV₃ w) ≫ ((L₀.mul (pullback.fst f₀ f₀ ≫ f₀) ⟨pullback.fst f₀ f₀, rfl⟩ ⟨pullback.snd f₀ f₀, pullback.condition.symm⟩).1 ∣_ 𝒰.U (lam₃ w)) ≫ g (lam₃ w)) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_product_local_lifts_of_local_lifts.solution
