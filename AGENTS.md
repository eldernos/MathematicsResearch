# Writing the GitHub README

- Write for a mathematician opening the repository for the first time. Lead with a self-contained theorem, define its notation, and link the Lean statement and a human-readable proof. Keep extended examples and proof details in the linked notes.
- Use ordinary prose, italic variables and Unicode relations for short inline expressions. Put displayed equations in a fenced `math` block on separate lines, using elementary notation such as sums and fractions. Keep headings, link labels and tables readable without a math renderer.
- Avoid `\operatorname`, `\substack`, custom macros, TeX environments and prose embedded with `\text` in the README. Define a set or a function in the preceding sentence to simplify a long formula.
- When changing formulas, check the rendered GitHub Markdown. Inspect the equations for lost braces, literal commands, missing symbols and clipping at narrow widths. A math container in the HTML alone does not establish that its contents typeset correctly.
- Identify the scope of each result. Link kernel-verified theorems, paper deductions and finite computations to their respective evidence.
