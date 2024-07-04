use pyo3::prelude::*;
/// Computes the convex hull of a set of 2D points using Graham's scan algorithm.
///
/// # Arguments
///
/// * `points` - A mutable vector of tuples representing the points (x, y).
///
/// # Returns
///
/// A vector of tuples representing the points that form the convex hull in counter-clockwise order.
pub fn convex_hull(points: &mut Vec<(f64, f64)>) -> Vec<(f64, f64)> {
    points.sort_by(|a, b| a.partial_cmp(b).unwrap());

    let mut lower = Vec::new();
    for &p in points.iter() {
        while lower.len() >= 2 && cross(lower[lower.len()-2], lower[lower.len()-1], p) <= 0.0 {
            lower.pop();
        }
        lower.push(p);
    }

    let mut upper = Vec::new();
    for &p in points.iter().rev() {
        while upper.len() >= 2 && cross(upper[upper.len()-2], upper[upper.len()-1], p) <= 0.0 {
            upper.pop();
        }
        upper.push(p);
    }

    lower.pop();
    upper.pop();
    lower.append(&mut upper);
    lower
}
/// Computes the cross product of vectors OA and OB. A positive cross product indicates a counter-clockwise turn,
/// a negative cross product indicates a clockwise turn, and zero indicates that the points are collinear.
///
/// # Arguments
///
/// * `o` - The origin point (x, y).
/// * `a` - The first point (x, y).
/// * `b` - The second point (x, y).
///
/// # Returns
///
/// The cross product of vectors OA and OB.
fn cross(o: (f64, f64), a: (f64, f64), b: (f64, f64)) -> f64 {
    (a.0 - o.0) * (b.1 - o.1) - (a.1 - o.1) * (b.0 - o.0)
}
/// Computes the convex hull of a set of 2D points and returns it as a list of points.
///
/// This function serves as the Python interface for the convex hull computation, 
/// accepting a list of tuples from Python and returning the result as a list of tuples.
///
/// # Arguments
///
/// * `points` - A list of tuples representing the points (x, y).
///
/// # Returns
///
/// A list of tuples representing the points that form the convex hull in counter-clockwise order.
#[pyfunction]
pub fn Convex_hull(py: Python, points: Vec<(f64, f64)>) -> PyResult<Vec<(f64, f64)>> {
    let mut points = points;
    let result = convex_hull(&mut points);
    Ok(result)
}