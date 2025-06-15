# [Under Construction]

## About

## Setup

The compiler tool requires a working [OCaml](https://ocaml.org/) compiler (5.3.0 or higher), along with a few additional packages. 

The suggested approach to set up the required dependencies and running the tool is to use [opam](https://opam.ocaml.org/) (a package manager for OCaml) along with [Dune](https://dune.readthedocs.io/en/latest/) (a build system for OCaml).

Instructions on how to install opam can be found [here](https://opam.ocaml.org/doc/Install.html).

From the root directory of this project, create a local OCaml environment (a *switch*) to manage 
this project's dependencies.
```
opam update && opam switch create .
```

To confirm the switch is now active:
```
opam switch
```

**Dune**, along with the remaining dependencies, should now be installed.

### Building
 
To build the project:
```
dune build
```

To clean up the artifacts from a previous build
```
dune clean
```

### Running

After building, the compiler can be tested with one of the choreography examples available in 
the **examples** folder:
```
dune exec main < ./examples/hello_swarm
```

To run the test suite:
```bash
dune runtest
```