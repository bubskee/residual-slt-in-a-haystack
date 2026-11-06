module
import ResidualSLT

noncomputable section
namespace ResidualSLT.Examples
open MeasureTheory Set

/-- The nonsingular integral is the area of the square. -/
theorem critical_sector_zero : criticalSectorMellin 0 = 1 := by
  rw [criticalSectorMellin_eq 0 (by norm_num)]
  norm_num

/-- A genuinely singular, convergent square integral has exact value three. -/
theorem critical_sector_quarter :
    (∫ z : ℝ × ℝ in cancellationRectangle, criticalSectorLoss z ^ (-(1 / 4 : ℝ))) = 3 := by
  rw [← criticalSectorMellin_eq_square_integral (1 / 4) (by norm_num),
    criticalSectorMellin_eq (1 / 4) (by norm_num)]
  norm_num

end ResidualSLT.Examples
#print axioms ResidualSLT.Examples.critical_sector_zero
#print axioms ResidualSLT.Examples.critical_sector_quarter
