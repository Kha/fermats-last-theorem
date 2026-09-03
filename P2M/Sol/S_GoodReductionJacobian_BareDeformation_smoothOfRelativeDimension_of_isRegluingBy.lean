import Mathlib
import Definitions.Def_GoodReductionJacobian_BareDeformation
import Definitions.Def_GoodReductionJacobian_IsRegluingBy
import P2M.Util
namespace P2MW.S_GoodReductionJacobian_BareDeformation_smoothOfRelativeDimension_of_isRegluingBy

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem solution
    {S : Type} [CommRing S] {Aₛ : Scheme.{0}} {fₛ : Aₛ ⟶ Spec (CommRingCat.of S)} {Lₛ : RelativeGroupLaw S fₛ}
    {B : Type} [CommRing B] [Algebra B S]
    (D₀ : BareDeformation fₛ Lₛ B) (𝒰 : D₀.A.OrderedAffineCover)
    (τ : ∀ s : 𝒰.Idx 1, ((↑(𝒰.inter s) : Scheme.{0}) ≅ ↑(𝒰.inter s)))
    (D : BareDeformation fₛ Lₛ B) (hD : D₀.IsRegluingBy 𝒰 τ D)
    (n : ℕ) [SmoothOfRelativeDimension n D₀.f] :
    SmoothOfRelativeDimension n D.f := by
  obtain ⟨-, -, ιD, hιopen, hιf, hιsurj, -, -⟩ := hD
  haveI : ∀ i, IsOpenImmersion (ιD i) := hιopen
  let 𝒱 : D.A.OpenCover := Scheme.Cover.mkOfCovers 𝒰.ι (fun i => (↑(𝒰.U i) : Scheme.{0})) ιD hιsurj
  rw [IsZariskiLocalAtSource.iff_of_openCover (P := @SmoothOfRelativeDimension n) 𝒱]
  intro i
  show SmoothOfRelativeDimension n (ιD i ≫ D.f)
  rw [hιf i]
  exact IsZariskiLocalAtSource.comp (P := @SmoothOfRelativeDimension n) inferInstance (𝒰.U i).ι
