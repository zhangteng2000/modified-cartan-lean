import ModifiedCartan.CartanFourLocal
import ModifiedCartan.CartanDiagonal

noncomputable section
set_option autoImplicit false
namespace ModifiedCartan

/-- Classical Cartan extraction for four holomorphic units on the entire
open unit disk, with one common strict subsequence. -/
theorem cartanExtraction_four : CartanExtractionAt 4 :=
  cartanExtraction_of_local (fun _ hf hs _ hL hL1 => cartan_four_local hf hs hL hL1)

end ModifiedCartan
