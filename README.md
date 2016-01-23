A software verification tool for Simple-C programs with multiple procedures, loops and calls.

Initially, the tool was built to only support programs with a single procedure and no loops. It employs standard verification techniques such as converting the program to static single assignment form, applying predication to handle conditionals and translating the result to an SMT-LIB formula that is passed to the Z3 SMT solver.

We support calls via procedure summarisation and loops via Houdini with invariant inference and Bounded Model Checking with custom loop unwinding. We also use fuzz testing by compiling programs to C++ and running them to find failing assertions.

