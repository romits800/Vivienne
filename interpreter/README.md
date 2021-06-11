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
To initialize opam and install OCaml version 4.06.0 run:

```bash
$ opam init 
$ opam switch 4.06.0
```

Install the following dependencies:
```bash
$ sudo apt-get install libgmp-dev python2.7
```

Then, install the following packages with opam:
```bash
$ opam install ocamlbuild z3 menhir num
```

### Z3 OCaml bindings

Vivienne requires additionally the installation of z3 OCaml bindings:

```bash
$ opam install z3
```

Or compile from [source](https://github.com/Z3Prover/z3) using:

```bash
$ python scripts/mk_make.py --ml
$ cd build
$ make -j 8
```

### Z3 OCaml bindings

Vivienne requires the following solvers (binaries) to be available in the $PATH:

- [z3](https://github.com/Z3Prover/z3) 
- [boolector](https://github.com/Boolector/boolector/releases) 
- [yices-smt2](https://github.com/SRI-CSL/yices2)
- [cvc4-1.8-x86_64-linux-opt](https://cvc4.github.io/downloads.html)

### Environmental Variables
Vivienne expects this path in environmental variable $VIV_PATH:

```bash
$ export VIV_PATH=/path/to/interpreter/directory/
```

## Install
To install Vivienne run:
```bash
$ make
```
If you get the following error:
> ocamlopt.opt: unknown option '-cclib -lstdc++'.

You need to modify the META file of z3 (e.g. in `${HOME}/.opam/4.06.0/lib/z3/META`)
and replace:
```
linkopts = '-cclib -lstdc++'
```
with
```
linkopts = ''
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

