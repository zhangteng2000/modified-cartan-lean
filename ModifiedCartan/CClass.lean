import ModifiedCartan.Hurwitz
import ModifiedCartan.Montel

noncomputable section
set_option autoImplicit false
namespace ModifiedCartan

/-- The connected-domain two-dominant-index assertion from Section 1, including
the actual simultaneous subsequence extraction. Connectedness is not part of
the definition of a C-class. -/
theorem cclass_two_dominants_after_extraction {p : ℕ} {f : Family p}
    {I : Finset (Fin p)} {U : Set ℂ}
    (hU : IsOpen U) (hconn : IsConnected U)
    (hf : ∀ i n, IsHolomorphicUnit (f i n) U) (hI : IsCClass f I U) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ k l : Fin p,
      k ≠ l ∧ IsDominant (subsequence f φ) I U k ∧ IsDominant (subsequence f φ) I U l := by
  classical
  obtain ⟨k, hk⟩ := hI
  obtain ⟨φ, hφ, hlimits⟩ := finite_montel_subsequence I
    (fun j n z => f j n z / f k n z) hU
    (fun j _ n => (hf j n).1.div (hf k n).1 (hf k n).2) hk.2.1
  choose! H hdH hlimH using hlimits
  have hks := dominant_subsequence hk hφ
  obtain ⟨l, hlk, hls⟩ := cclass_two_dominants_of_quotient_limits hU hconn
    (fun i n => hf i (φ n)) hks hlimH
  exact ⟨φ, hφ, k, l, Ne.symm hlk, hks, hls⟩

end ModifiedCartan
