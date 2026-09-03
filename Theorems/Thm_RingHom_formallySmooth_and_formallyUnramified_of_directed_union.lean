import Mathlib
import P2M.Util
import P2M.Sol.S_RingHom_formallySmooth_and_formallyUnramified_of_directed_union

set_option autoImplicit false

theorem RingHom.formallySmooth_and_formallyUnramified_of_directed_union
    {ι : Type} [Nonempty ι] (r : ι → ι → Prop) (hdir : ∀ i j, ∃ k, r i k ∧ r j k)
    {A S : Type} [CommRing A] [CommRing S]
    (An Sn : ι → Type) [∀ i, CommRing (An i)] [∀ i, CommRing (Sn i)]
    (a : ∀ i, An i →+* A) (s : ∀ i, Sn i →+* S) (hs : ∀ i, Function.Injective (s i))
    (aa : ∀ i j, r i j → (An i →+* An j)) (ss : ∀ i j, r i j → (Sn i →+* Sn j))
    (haa : ∀ i j (h : r i j), (a j).comp (aa i j h) = a i) (hss : ∀ i j (h : r i j), (s j).comp (ss i j h) = s i)
    (hcovA : ∀ x : A, ∃ i y, a i y = x) (hcovS : ∀ x : S, ∃ i y, s i y = x)
    (φn : ∀ i, Polynomial (An i) →+* Sn i)
    (hφs : ∀ i, (φn i).FormallySmooth) (hφu : ∀ i, (φn i).FormallyUnramified)
    (hφn : ∀ i j (h : r i j), (ss i j h).comp (φn i) = (φn j).comp (Polynomial.mapRingHom (aa i j h)))
    (φ : Polynomial A →+* S) (hφ : ∀ i, (s i).comp (φn i) = φ.comp (Polynomial.mapRingHom (a i))) :
    φ.FormallySmooth ∧ φ.FormallyUnramified := by p2m_exact_reverting @_root_.P2MW.S_RingHom_formallySmooth_and_formallyUnramified_of_directed_union.solution
