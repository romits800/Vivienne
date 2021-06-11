# Vivienne: WebAssembly Relational Symbolic Execution

Vivienne is a tool for Relational Symbolic Execution of WebAssembly code. 

## Prerequisites 

For compiling Vivienne, you need to make sure that you have the following 
prerequisites.

### OCaml
Vivienne is tested with OCaml version 4.06.
To install the OCaml build system using opam run:
```bash
$ sudo apt-get install opam
```
Install OCaml version 4.06.0:

```bash
$ opam switch 4.06.0
```
Install the following packages with opam:
```bash
$ opam install z3 num unix menhir
```

### Z3 OCaml bindings

Vivienne requires additionally the installation of z3 OCaml bindings:

```bash
$ opam install z3
```

Or compile from [source](https://github.com/Z3Prover/z3) using:

```bash
$ python scripts/mk_make.py --ml
```

### Z3 OCaml bindings

Vivienne requires the following solvers to be available in the $PATH:

- z3
- boolector
- yices-smt2
- cvc4

### Environmental Variables
Vivienne expects this path in environmental variable $VIV_PATH:

```bash
$ export VIV_PATH=/bash/to/path/interpreter/
```

## Install
To install Vivienne run:
```bash
$ make
```
### Test
To test Vivienne run:
```bash
$ make test-symb
```

### Run
To run a program with loop unrolling, run:
```bash
$ ./wasm -t -i ../test/symb/script_tea_pass.wast
```
To run a program with the automatic invariant, run:
```bash
$ ./wasm -t -l -i ../test/symb/script_tea_pass.wast
```

