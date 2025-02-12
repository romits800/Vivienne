# Relational Symbolic Execution for WebAssembly (based on spec)

This repository contains the source for the Vivienne, a WebAssembly
Relational Symbolic Execution implementation for identifying constant-time
vulnerabilities or verifying constant-time programs.

This implementation is based on the reference interpreter for WebAssembly in
OCaml. 
A formatted version of the spec is available here:
[webassembly.github.io/spec](https://webassembly.github.io/spec/),

# Vivienne

To compile Vivienne, move to directory "interpreter" and run `make`. 
To compile and run Vivienne, there is a number of prerequisites described in interpreter/README.md.

```bash
cd interpreter
make

```
# Experiments

The experiments used in our paper are available at [Vivienne_eval](https://github.com/romits800/Vivienne_eval). 

## citing

For citing WebAssembly in LaTeX, use [this bibtex file](wasm-specs.bib).

For citing Vivienne in LaTeX, use [this bibtex file](vivienne.bib)
