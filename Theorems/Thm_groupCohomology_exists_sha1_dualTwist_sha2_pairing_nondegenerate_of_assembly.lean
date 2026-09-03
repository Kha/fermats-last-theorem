import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import P2M.Util
import P2M.Sol.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_assembly

set_option autoImplicit false
set_option maxHeartbeats 1600000
open CategoryTheory Module groupCohomology ExtCitation

theorem groupCohomology.exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_assembly
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes)
    (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) [FiniteDimensional (ZMod p) M]

    (θ : ∀ v : extArithIndex S,
      continuousH1 (extArithLoc S v) (Rep.res (extArithLoc S v) M) →ₗ[ZMod p]
        Module.Dual (ZMod p) (continuousH1 (extArithLoc S v) (Rep.res (extArithLoc S v) (M.dualTwist (cycloChar p)))))
    (hθ : ∀ v, Function.Bijective (θ v))

    [FiniteDimensional (ZMod p) ↥(continuousH1S S (M.dualTwist (cycloChar p)))]
    (hloc : ∀ y ∈ continuousH1S S (M.dualTwist (cycloChar p)), ∀ v : extArithIndex S,
      locTotal (extArithLoc S) (M.dualTwist (cycloChar p)) y v ∈ continuousH1 (extArithLoc S v) (Rep.res (extArithLoc S v) (M.dualTwist (cycloChar p))))

    {G : Type} [Group G] {R P : Rep ℤ G} (f : R ⟶ P)
    (E J Y C : Rep ℤ G) (iEJ : E ⟶ J) (gJY : J ⟶ Y) (jYC : Y ⟶ C)
    (VB : Type) [AddCommGroup VB]
    (dY : (R ⟶ Y) →+ H1 ((ihom R).obj E))
    (LE2 : H1 ((ihom R).obj E) →+ continuousH2S S M)
    (LJ1 : (R ⟶ J) →+ (∀ v : extArithIndex S, continuousH1 (extArithLoc S v) (Rep.res (extArithLoc S v) M)))
    (al : (R ⟶ C) →+ (VB →+ ZMod p))

    (infl : VB →+ H1 (M.dualTwist (cycloChar p))) (hinj : Function.Injective infl)
    (hrange : ∀ y : H1 (M.dualTwist (cycloChar p)), y ∈ continuousH1S S (M.dualTwist (cycloChar p)) ↔ ∃ x, infl x = y)
    (hLESa : ∀ x : H1 ((ihom R).obj E), (groupCohomology.map (MonoidHom.id G) ((ihom R).map iEJ) 1).hom x = 0 → ∃ t, dY t = x)
    (hLESb : ∀ t : R ⟶ Y, dY t = 0 → ∃ s : R ⟶ J, t = s ≫ gJY)
    (hLESc : ∀ s : R ⟶ J, dY (s ≫ gJY) = 0)
    (hKERLOC : ∀ x : H1 ((ihom R).obj E), (∀ v, locRes₂S S M (extArithLoc S v) (LE2 x) = 0) →
      (groupCohomology.map (MonoidHom.id G) ((ihom R).map iEJ) 1).hom x = 0)
    (hSTAB : ∀ c : continuousH2S S M, c ∈ sha₂ S M → ∃ x, LE2 x = c)
    (hJ1 : Function.Surjective LJ1)
    (u : extArithIndex S → (ZMod p)ˣ)
    (hID : ∀ (s : R ⟶ J) (x : VB) (hx : infl x ∈ continuousH1S S (M.dualTwist (cycloChar p))),
      al (s ≫ gJY ≫ jYC) x = ∑ v, (u v : ZMod p) * θ v (LJ1 s v) ⟨locTotal (extArithLoc S) (M.dualTwist (cycloChar p)) (infl x) v, hloc _ hx v⟩)
    (hαsurj : ∀ g : VB →+ ZMod p, ∃ φ : R ⟶ C, al φ = g)

    {G₁ : Type} [Group G₁] {R₁ P₁ : Rep ℤ G₁} (f₁ : R₁ ⟶ P₁)
    (E₁ J₁ Y₁ C₁ : Rep ℤ G₁) (iEJ₁ : E₁ ⟶ J₁) (jYC₁ : Y₁ ⟶ C₁)
    (VB₁ : Type) [AddCommGroup VB₁]
    (dY₁ : (R₁ ⟶ Y₁) →+ H1 ((ihom R₁).obj E₁))
    (LE2₁ : H1 ((ihom R₁).obj E₁) →+ continuousH2S S M)
    (al₁ : (R₁ ⟶ C₁) →+ (VB₁ →+ ZMod p))

    (iY₁ : (R ⟶ Y) →+ (R₁ ⟶ Y₁)) (iC₁ : (R ⟶ C) →+ (R₁ ⟶ C₁))
    (i2₁ : H1 ((ihom R).obj E) →+ H1 ((ihom R₁).obj E₁))
    (iB₁ : VB →+ VB₁) (hiB₁ : Function.Surjective iB₁)
    (hiCj₁ : ∀ t : R ⟶ Y, iC₁ (t ≫ jYC) = iY₁ t ≫ jYC₁)
    (hid₁ : ∀ t : R ⟶ Y, dY₁ (iY₁ t) = i2₁ (dY t))
    (hiL₁ : ∀ x, LE2₁ (i2₁ x) = LE2 x)
    (hial₁ : ∀ (φ : R ⟶ C) (x : VB), al₁ (iC₁ φ) (iB₁ x) = al φ x)

    (hEXF : ∀ φ : R ⟶ C, (∃ χ : P₁ ⟶ C₁, iC₁ φ = f₁ ≫ χ) ∨ (∃ x : VB₁, al₁ (iC₁ φ) x ≠ 0))
    (hPITco : ∀ φ : R ⟶ C, ∃ (t : R₁ ⟶ Y₁) (χ : P₁ ⟶ C₁), iC₁ φ = t ≫ jYC₁ + f₁ ≫ χ)
    (hαext₁ : ∀ χ : P₁ ⟶ C₁, al₁ (f₁ ≫ χ) = 0)
    (hLESe₁ : ∀ t : R₁ ⟶ Y₁, (groupCohomology.map (MonoidHom.id G₁) ((ihom R₁).map iEJ₁) 1).hom (dY₁ t) = 0)
    (hKERLOC₁ : ∀ x : H1 ((ihom R₁).obj E₁), (groupCohomology.map (MonoidHom.id G₁) ((ihom R₁).map iEJ₁) 1).hom x = 0 →
      ∀ v, locRes₂S S M (extArithLoc S v) (LE2₁ x) = 0)

    {G₂ : Type} [Group G₂] {R₂ P₂ : Rep ℤ G₂} (f₂ : R₂ ⟶ P₂)
    (E₂ J₂ Y₂ C₂ : Rep ℤ G₂) (iEJ₂ : E₂ ⟶ J₂) (gJY₂ : J₂ ⟶ Y₂) (jYC₂ : Y₂ ⟶ C₂)
    (VB₂ : Type) [AddCommGroup VB₂]
    (dY₂ : (R₂ ⟶ Y₂) →+ H1 ((ihom R₂).obj E₂))
    (LE2₂ : H1 ((ihom R₂).obj E₂) →+ continuousH2S S M)
    (LJ1₂ : (R₂ ⟶ J₂) →+ (∀ v : extArithIndex S, continuousH1 (extArithLoc S v) (Rep.res (extArithLoc S v) M)))
    (al₂ : (R₂ ⟶ C₂) →+ (VB₂ →+ ZMod p))

    (iY₂ : (R₁ ⟶ Y₁) →+ (R₂ ⟶ Y₂)) (iC₂ : (R₁ ⟶ C₁) →+ (R₂ ⟶ C₂))
    (i2₂ : H1 ((ihom R₁).obj E₁) →+ H1 ((ihom R₂).obj E₂))
    (iB₂ : VB₁ →+ VB₂) (hiB₂ : Function.Surjective iB₂)
    (hiCj₂ : ∀ t : R₁ ⟶ Y₁, iC₂ (t ≫ jYC₁) = iY₂ t ≫ jYC₂)
    (hid₂ : ∀ t : R₁ ⟶ Y₁, dY₂ (iY₂ t) = i2₂ (dY₁ t))
    (hiL₂ : ∀ x, LE2₂ (i2₂ x) = LE2₁ x)
    (hial₂ : ∀ (φ : R₁ ⟶ C₁) (x : VB₁), al₂ (iC₂ φ) (iB₂ x) = al₁ φ x)

    (hPITker : ∀ (t : R₁ ⟶ Y₁) (χ : P₁ ⟶ C₁), t ≫ jYC₁ = f₁ ≫ χ → ∃ χ' : P₂ ⟶ Y₂, iY₂ t = f₂ ≫ χ')
    (hB3ker : ∀ x : H1 ((ihom R₁).obj E₁), LE2₁ x = 0 → i2₂ x = 0)
    (hLESb₂ : ∀ t : R₂ ⟶ Y₂, dY₂ t = 0 → ∃ s : R₂ ⟶ J₂, t = s ≫ gJY₂)
    (hLESd₂ : ∀ (t : R₂ ⟶ Y₂) (χ : P₂ ⟶ Y₂), dY₂ (t + f₂ ≫ χ) = dY₂ t)
    (u₂ : extArithIndex S → (ZMod p)ˣ)
    (hID₂ : ∀ (s : R₂ ⟶ J₂) (x : VB) (hx : infl x ∈ continuousH1S S (M.dualTwist (cycloChar p))),
      al₂ (s ≫ gJY₂ ≫ jYC₂) (iB₂ (iB₁ x)) = ∑ v, (u₂ v : ZMod p) * θ v (LJ1₂ s v) ⟨locTotal (extArithLoc S) (M.dualTwist (cycloChar p)) (infl x) v, hloc _ hx v⟩) :
    ∃ B : sha₁ S (M.dualTwist (cycloChar p)) →ₗ[ZMod p] sha₂ S M →ₗ[ZMod p] ZMod p,
      (∀ y, (∀ x, B y x = 0) → y = 0) ∧ (∀ x, (∀ y, B y x = 0) → x = 0) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_assembly.solution
