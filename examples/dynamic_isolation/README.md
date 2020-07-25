# Development workflow to avoid performance issues
- In Interfaces.v, replace "Instance FiniteType..." with "Declare Instance" for cases marked "SLOW"
- In main Makefile,
  replace
    ```dune exec -- cuttlec "${BUILD_DIR}/$@/$(notdir $(<:.v=.ml))" -T all -o "$@"``` 
  with
    ```dune exec -- cuttlec "${BUILD_DIR}/$@/$(notdir $(<:.v=.ml))" -T cpp,hpp,opt -o "$@" ```
  to avoid slow Verilog compile times (> 20 min?)


