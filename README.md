Build this project
```bash
dune build
```

Build javascript file
```bash 
dune build @js
```

Clear build files
```bash
dune clean
```

Run this project
```bash
dune exec tardis < <path-to-a-file>
```

Watch this project
```bash
dune build --watch --terminal-persistence=clear-on-rebuild
```

Test this project
```bash
dune runtest
```