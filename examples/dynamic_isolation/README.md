* `make DUT=rv32i_no_sm`
* generated targets in `_objects/rv32i_no_sm.v` should be able to run tests in `tests/_build/rv32i_no_sm`
* There, original single-core RV tests were crudely ported to multicore system by having the second core spin instead of exiting
* tests in `tests/_build/rv32i_no_sm/multicore_no_sm` have both cores running programs (e.g. in primes, both run the primes code)
* The `shared_memory` test in `tests/multicore_no_sm/shared_memory` is a starting point to experiment with programs where a cache coherence protocol is actually relevant 


