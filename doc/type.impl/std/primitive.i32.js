(function() {var type_impls = {
"pyo3":[["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-Element-for-i32\" class=\"impl\"><a class=\"src rightside\" href=\"src/pyo3/buffer.rs.html#694\">source</a><a href=\"#impl-Element-for-i32\" class=\"anchor\">§</a><h3 class=\"code-header\">impl <a class=\"trait\" href=\"pyo3/buffer/trait.Element.html\" title=\"trait pyo3::buffer::Element\">Element</a> for <a class=\"primitive\" href=\"https://doc.rust-lang.org/1.78.0/std/primitive.i32.html\">i32</a></h3></section></summary><div class=\"impl-items\"><details class=\"toggle method-toggle\" open><summary><section id=\"method.is_compatible_format\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/pyo3/buffer.rs.html#694\">source</a><a href=\"#method.is_compatible_format\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"pyo3/buffer/trait.Element.html#tymethod.is_compatible_format\" class=\"fn\">is_compatible_format</a>(format: &amp;<a class=\"struct\" href=\"https://doc.rust-lang.org/1.78.0/core/ffi/c_str/struct.CStr.html\" title=\"struct core::ffi::c_str::CStr\">CStr</a>) -&gt; <a class=\"primitive\" href=\"https://doc.rust-lang.org/1.78.0/std/primitive.bool.html\">bool</a></h4></section></summary><div class='docblock'>Gets whether the element specified in the format string is potentially compatible.\nAlignment and size are checked separately from this function.</div></details></div></details>","Element","pyo3::ffi::PY_INT32_T","pyo3::ffi::Py_UNICODE"],["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-FromPyObject%3C'py%3E-for-i32\" class=\"impl\"><a class=\"src rightside\" href=\"src/pyo3/conversions/std/num.rs.html#148\">source</a><a href=\"#impl-FromPyObject%3C'py%3E-for-i32\" class=\"anchor\">§</a><h3 class=\"code-header\">impl&lt;'py&gt; <a class=\"trait\" href=\"pyo3/conversion/trait.FromPyObject.html\" title=\"trait pyo3::conversion::FromPyObject\">FromPyObject</a>&lt;'py&gt; for <a class=\"primitive\" href=\"https://doc.rust-lang.org/1.78.0/std/primitive.i32.html\">i32</a></h3></section></summary><div class=\"impl-items\"><details class=\"toggle method-toggle\" open><summary><section id=\"method.extract_bound\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/pyo3/conversions/std/num.rs.html#148\">source</a><a href=\"#method.extract_bound\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"pyo3/conversion/trait.FromPyObject.html#method.extract_bound\" class=\"fn\">extract_bound</a>(obj: &amp;<a class=\"struct\" href=\"pyo3/prelude/struct.Bound.html\" title=\"struct pyo3::prelude::Bound\">Bound</a>&lt;'_, <a class=\"struct\" href=\"pyo3/types/struct.PyAny.html\" title=\"struct pyo3::types::PyAny\">PyAny</a>&gt;) -&gt; <a class=\"type\" href=\"pyo3/prelude/type.PyResult.html\" title=\"type pyo3::prelude::PyResult\">PyResult</a>&lt;Self&gt;</h4></section></summary><div class='docblock'>Extracts <code>Self</code> from the bound smart pointer <code>obj</code>. <a href=\"pyo3/conversion/trait.FromPyObject.html#method.extract_bound\">Read more</a></div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.extract\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/pyo3/conversion.rs.html#218-220\">source</a><a href=\"#method.extract\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"pyo3/conversion/trait.FromPyObject.html#method.extract\" class=\"fn\">extract</a>(ob: &amp;'py <a class=\"struct\" href=\"pyo3/types/struct.PyAny.html\" title=\"struct pyo3::types::PyAny\">PyAny</a>) -&gt; <a class=\"type\" href=\"pyo3/prelude/type.PyResult.html\" title=\"type pyo3::prelude::PyResult\">PyResult</a>&lt;Self&gt;</h4></section></summary><div class='docblock'>Extracts <code>Self</code> from the source GIL Ref <code>obj</code>. <a href=\"pyo3/conversion/trait.FromPyObject.html#method.extract\">Read more</a></div></details></div></details>","FromPyObject<'py>","pyo3::ffi::PY_INT32_T","pyo3::ffi::Py_UNICODE"],["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-IntoPy%3CPy%3CPyAny%3E%3E-for-i32\" class=\"impl\"><a class=\"src rightside\" href=\"src/pyo3/conversions/std/num.rs.html#148\">source</a><a href=\"#impl-IntoPy%3CPy%3CPyAny%3E%3E-for-i32\" class=\"anchor\">§</a><h3 class=\"code-header\">impl <a class=\"trait\" href=\"pyo3/conversion/trait.IntoPy.html\" title=\"trait pyo3::conversion::IntoPy\">IntoPy</a>&lt;<a class=\"struct\" href=\"pyo3/prelude/struct.Py.html\" title=\"struct pyo3::prelude::Py\">Py</a>&lt;<a class=\"struct\" href=\"pyo3/types/struct.PyAny.html\" title=\"struct pyo3::types::PyAny\">PyAny</a>&gt;&gt; for <a class=\"primitive\" href=\"https://doc.rust-lang.org/1.78.0/std/primitive.i32.html\">i32</a></h3></section></summary><div class=\"impl-items\"><details class=\"toggle method-toggle\" open><summary><section id=\"method.into_py\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/pyo3/conversions/std/num.rs.html#148\">source</a><a href=\"#method.into_py\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"pyo3/conversion/trait.IntoPy.html#tymethod.into_py\" class=\"fn\">into_py</a>(self, py: <a class=\"struct\" href=\"pyo3/marker/struct.Python.html\" title=\"struct pyo3::marker::Python\">Python</a>&lt;'_&gt;) -&gt; <a class=\"type\" href=\"pyo3/prelude/type.PyObject.html\" title=\"type pyo3::prelude::PyObject\">PyObject</a></h4></section></summary><div class='docblock'>Performs the conversion.</div></details></div></details>","IntoPy<Py<PyAny>>","pyo3::ffi::PY_INT32_T","pyo3::ffi::Py_UNICODE"],["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-ToPyObject-for-i32\" class=\"impl\"><a class=\"src rightside\" href=\"src/pyo3/conversions/std/num.rs.html#148\">source</a><a href=\"#impl-ToPyObject-for-i32\" class=\"anchor\">§</a><h3 class=\"code-header\">impl <a class=\"trait\" href=\"pyo3/conversion/trait.ToPyObject.html\" title=\"trait pyo3::conversion::ToPyObject\">ToPyObject</a> for <a class=\"primitive\" href=\"https://doc.rust-lang.org/1.78.0/std/primitive.i32.html\">i32</a></h3></section></summary><div class=\"impl-items\"><details class=\"toggle method-toggle\" open><summary><section id=\"method.to_object\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/pyo3/conversions/std/num.rs.html#148\">source</a><a href=\"#method.to_object\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"pyo3/conversion/trait.ToPyObject.html#tymethod.to_object\" class=\"fn\">to_object</a>(&amp;self, py: <a class=\"struct\" href=\"pyo3/marker/struct.Python.html\" title=\"struct pyo3::marker::Python\">Python</a>&lt;'_&gt;) -&gt; <a class=\"type\" href=\"pyo3/prelude/type.PyObject.html\" title=\"type pyo3::prelude::PyObject\">PyObject</a></h4></section></summary><div class='docblock'>Converts self into a Python object.</div></details></div></details>","ToPyObject","pyo3::ffi::PY_INT32_T","pyo3::ffi::Py_UNICODE"]],
"pyo3_ffi":[]
};if (window.register_type_impls) {window.register_type_impls(type_impls);} else {window.pending_type_impls = type_impls;}})()