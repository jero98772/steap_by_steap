use pyo3::prelude::*;

/// Represents a line segment between two points.
#[pyclass]
pub struct LineSegment {
    startx: f64,
    endx: f64,
    starty: f64,
    endy: f64,

}

#[pymethods]
impl LineSegment {
    #[new]
    fn new(startx: f64,starty: f64, endx: f64, endy: f64) -> Self {
        LineSegment {startx,starty, endx, endy}
    }

    /// Calculates the length of the line segment.
    ///
    /// Returns:
    /// - `f64`: Length of the line segment.
    fn length(&self) -> f64 {
        ((self.endx - self.startx).powi(2) + (self.endy - self.starty).powi(2)).sqrt()
    }

    /// Calculates the midpoint of the line segment.
    ///
    /// Returns:
    /// - `Point`: Midpoint of the line segment.
    fn midpoint(&self) -> (f64,f64) {
            ((self.startx + self.endx) / 2.0,(self.starty + self.endy) / 2.0)
    }
}

