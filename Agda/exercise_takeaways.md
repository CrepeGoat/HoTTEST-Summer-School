# Agda
- Agda is VERY sensitive to whitespace!
    - indentation matters (like in Python)
    - space is required between any identifiers/delimiters
    - space is *not allowed* around underscores in mixfix operators
- constructors can be applied in *reverse order* using the dot syntax
    - e.g., `pr1 x` is the same as `x .pr1`
    - the change in order can remove parentheses from long expressions
- the `with` syntax allows you to case-split (C-c C-c) on *arbitrary expressions*, as opposed to just variables
    - Note: this is sensitive to whitespace; the cases should be left-aligned with the original statement
- the `where` statement lets you define local objects/functions for a particular definition

# Type Theory
- **proof by contradiction**
    - IF you can somehow generate an element of the empty type (e.g., you have `f : A -> 0` and also `a : A`)
    - THEN you can use `0-elim` to generate a term of *any* type from the `0` term (i.e., `0-elim {A} : 0 -> A`) 
- **working with equality types**
    - `refl` builds equality between two judgementally equal types
    - can assert equality through `cong : x = x -> (f x) = (f x)` (a.k.a. `ap`)
    - can use a term of `x = y` by *case-splitting* on it, which will replace all instances of `x` with `y` (or vice-versa) 