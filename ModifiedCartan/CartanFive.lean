import ModifiedCartan.CartanFiveLocal
import ModifiedCartan.CartanDiagonal

noncomputable section
set_option autoImplicit false
namespace ModifiedCartan

/-- Classical Cartan extraction for five holomorphic units on the entire
open unit disk, with one common strict subsequence. -/
theorem cartanExtraction_five : CartanExtractionAt 5 :=
  cartanExtraction_of_local (fun _ hf hs _ hL hL1 => cartan_five_local hf hs hL hL1)

end ModifiedCartan
